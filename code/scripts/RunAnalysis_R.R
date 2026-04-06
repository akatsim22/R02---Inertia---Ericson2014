# Replication translation of RunAnalysis.do from Stata to R
# Paper: Ericson, Keith. "Consumer Inertia and Firm Pricing in the Medicare Part D Prescription Drug Insurance Exchange"
#
# Requires:
#   - Data_main.dta
#   - Data_subsidyinfo.dta
# Produces:
#   - CSV tables in Analysis_output/
#   - PNG figures in Analysis_output/
#
# Notes:
#   - This is a close translation, not a line-by-line byte-identical reproduction.
#   - Stata's outreg2/XML and .gph outputs are replaced with CSV and PNG outputs.
#   - Some Stata factor-variable conventions are implemented with fixest formulas.
#   - Cluster-robust SEs are computed at the firmID level.

suppressPackageStartupMessages({
  library(haven)
  library(dplyr)
  library(tidyr)
  library(stringr)
  library(purrr)
  library(fixest)
  library(ggplot2)
  library(modelsummary)
  library(readr)
})

options(stringsAsFactors = FALSE)
dir.create("Analysis_output", showWarnings = FALSE)

# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------

make_01 <- function(x) ifelse(is.na(x), 0, ifelse(x == 1, 1, 0))

safe_log <- function(x) ifelse(is.na(x) | x <= 0, NA_real_, log(x))

add_define_sample <- function(data, model, id_var = "uniqueID") {
  samp <- as.integer(!is.na(stats::model.frame(model)[[1]]))
  # fixest drops NAs before estimation, so align using rownames of model.frame
  idx <- as.integer(rownames(stats::model.frame(model)))
  data$inLastSampletemp <- 0L
  data$inLastSampletemp[idx] <- 1L
  data %>%
    group_by(.data[[id_var]]) %>%
    mutate(inLastSample = max(inLastSampletemp, na.rm = TRUE)) %>%
    ungroup() %>%
    select(-inLastSampletemp)
}

lag_by_group <- function(x, n = 1L) dplyr::lag(x, n = n)

write_model_table <- function(models, path, coef_omit = "(^state::|^firmID::|^year::|^yearOfPlan::|^btypedetail::|^L[0-4]btypedetail::)") {
  modelsummary::modelsummary(
    models,
    output = path,
    stars = TRUE,
    coef_omit = coef_omit,
    gof_omit = "IC|Log|Adj|AIC|BIC|RMSE|Std.Errors"
  )
}

# -----------------------------------------------------------------------------
# PART 1: Supplemental data
# -----------------------------------------------------------------------------

subsidies <- read_dta("Data_subsidyinfo.dta") %>%
  pivot_longer(
    cols = starts_with("s"),
    names_to = "year",
    values_to = "s"
  ) %>%
  mutate(year = readr::parse_number(year)) %>%
  arrange(PDPregion, year)

# -----------------------------------------------------------------------------
# PART 2: Prepare main data
# -----------------------------------------------------------------------------

main <- read_dta("Data_main.dta") %>%
  mutate(
    isin = 1L,
    firmID = as.integer(factor(orgParentCode)),
    uniqueIDNum = as.integer(factor(uniqueID))
  ) %>%
  group_by(firmID) %>%
  mutate(
    firstYrExist_F0 = min(year, na.rm = TRUE),
    thisPlansExist_F0 = ifelse(year > firstYrExist_F0, 1L, 0L)
  ) %>%
  ungroup() %>%
  group_by(firmID, state) %>%
  mutate(
    firstYrExistState_F0 = min(year, na.rm = TRUE),
    thisPlansExistState_F0 = ifelse(year > firstYrExistState_F0, 1L, 0L)
  ) %>%
  ungroup() %>%
  group_by(uniqueID) %>%
  mutate(minYear = min(year, na.rm = TRUE),
         maxYear = max(year, na.rm = TRUE)) %>%
  ungroup()

for (yr in 2006:2010) {
  main[[paste0("cohort", yr)]] <- ifelse(main$minYear == yr, 1L, 0L)
}
main$cohort <- main$minYear
main$yearOfPlan <- main$year - main$cohort + 1
main$yearOfPlan[main$yearOfPlan < 1] <- NA

# Year and year-of-plan dummies (Stata tab, gen())
year_dm <- model.matrix(~ factor(year) - 1, data = main) %>% as.data.frame()
names(year_dm) <- paste0("Dyear", seq_len(ncol(year_dm)))
yop_dm <- model.matrix(~ factor(yearOfPlan) - 1, data = main) %>% as.data.frame()
names(yop_dm) <- paste0("DOfPlan", seq_len(ncol(yop_dm)))
main <- bind_cols(main, year_dm, yop_dm)
if ("DOfPlan1" %in% names(main)) main <- main %>% rename(`_DOfPlan1` = DOfPlan1)
if ("Dyear1" %in% names(main)) main <- main %>% rename(`_Dyear1` = Dyear1)

main <- main %>%
  mutate(isBasic = ifelse(benefit == "B", 1L, 0L)) %>%
  group_by(uniqueID) %>%
  mutate(minIsBasic = min(isBasic, na.rm = TRUE)) %>%
  ungroup()

for (yr in 2007:2010) {
  nm <- paste0("minIsBasic", yr)
  main <- main %>%
    group_by(uniqueID) %>%
    mutate(!!nm := min(ifelse(year > yr, 1L, isBasic), na.rm = TRUE)) %>%
    ungroup()
}

main <- main %>%
  mutate(
    lnPremium = safe_log(premium),
    DS = ifelse(btypedetail == "DS", 1L, 0L),
    AE = ifelse(btypedetail == "AE", 1L, 0L)
  )

for (y in 2006:2010) {
  main[[paste0("AE", y)]] <- ifelse(main$year == y & main$btypedetail == "AE", 1L, 0L)
  main[[paste0("DS", y)]] <- ifelse(main$year == y & main$btypedetail == "DS", 1L, 0L)
}

# Deductible groups
main <- main %>%
  mutate(
    cDeduct0 = as.integer(deductible == 0),
    cDeduct1_50 = as.integer(deductible > 0 & deductible <= 50),
    cDeduct51_100 = as.integer(deductible > 50 & deductible <= 100),
    cDeduct101_150 = as.integer(deductible > 100 & deductible <= 150),
    cDeduct151_200 = as.integer(deductible > 150 & deductible <= 200),
    cDeduct201_250 = as.integer(deductible > 200 & deductible <= 250),
    cDeduct251_300 = as.integer(deductible > 250 & deductible <= 300),
    cDeduct301_ = as.integer(deductible > 300 & !is.na(deductible))
  )

deduct_vars <- c("cDeduct0", "cDeduct1_50", "cDeduct51_100", "cDeduct101_150",
                 "cDeduct151_200", "cDeduct201_250", "cDeduct251_300", "cDeduct301_")
main[deduct_vars] <- lapply(main[deduct_vars], function(x) ifelse(is.na(x), 0L, x))

for (x in deduct_vars) {
  for (y in 2006:2010) {
    main[[paste0(x, y)]] <- ifelse(main$year == y, main[[x]], 0L)
    main[[paste0("BA", x, y)]] <- ifelse(main$year == y & main$btypedetail == "BA", main[[x]], 0L)
    main[[paste0("BA", x, y)]][is.na(main[[paste0("BA", x, y)]])] <- 0L
  }
}

chk <- rowSums(main[, deduct_vars], na.rm = TRUE)
stopifnot(all(chk[!is.na(main$deductible)] == 1))

# Lags
main <- main %>% arrange(uniqueIDNum, year) %>% group_by(uniqueIDNum)
for (L in 1:4) {
  main[[paste0("L", L, "btypedetail")]] <- lag_by_group(main$btypedetail, L)
  main[[paste0("L", L, "benefit")]] <- lag_by_group(main$benefit, L)
  main[[paste0("L", L, "deductible")]] <- lag_by_group(main$deductible, L)
  main[[paste0("L", L, "premium")]] <- lag_by_group(main$premium, L)
  main[[paste0("L", L, "LIS")]] <- lag_by_group(main$LIS, L)
}
main$L0btypedetail <- main$btypedetail
main$L0benefit <- main$benefit
main$L0deductible <- main$deductible
main$L0premium <- main$premium
main$L0LIS <- main$LIS
main <- ungroup(main)

for (L in 0:4) {
  bt <- paste0("L", L, "btypedetail")
  ben <- paste0("L", L, "benefit")
  ded <- paste0("L", L, "deductible")
  main[[paste0("L", L, "DS")]] <- ifelse(main[[bt]] == "DS", 1L, 0L)
  main[[paste0("L", L, "AE")]] <- ifelse(main[[bt]] == "AE", 1L, 0L)
  main[[paste0("L", L, "BA_0")]] <- as.integer(main[[ded]] == 0 & main[[bt]] == "BA")
  main[[paste0("L", L, "BA_1_99")]] <- as.integer(main[[ded]] > 0 & main[[ded]] < 100 & main[[bt]] == "BA")
  main[[paste0("L", L, "BA_100")]] <- as.integer(main[[ded]] == 100 & main[[bt]] == "BA")
  main[[paste0("L", L, "BA_101_99")]] <- as.integer(main[[ded]] > 100 & main[[ded]] < 200 & main[[bt]] == "BA")
  main[[paste0("L", L, "BA_200_49")]] <- as.integer(main[[ded]] >= 200 & main[[ded]] < 250 & main[[bt]] == "BA")
  main[[paste0("L", L, "BA_250Up")]] <- as.integer(main[[ded]] >= 250 & !is.na(main[[ded]]) & main[[bt]] == "BA")

  lagcat <- c(paste0("L", L, "DS"), paste0("L", L, "AE"), paste0("L", L, "BA_0"),
              paste0("L", L, "BA_1_99"), paste0("L", L, "BA_100"), paste0("L", L, "BA_101_99"),
              paste0("L", L, "BA_200_49"), paste0("L", L, "BA_250Up"))
  s <- rowSums(main[, lagcat], na.rm = TRUE)
  idx <- main[[ben]] == "B" & !is.na(main[[bt]]) & main[[bt]] != ""
  stopifnot(all(s[idx] == 1))
}

# Enrollment shares
main <- main %>%
  group_by(state, year) %>%
  mutate(
    stateYrEnroll = sum(enrollment, na.rm = TRUE),
    share = enrollment / stateYrEnroll,
    lnS = safe_log(share),
    enrollmentNonLIS = enrollment - enrollmentLIS,
    stateYrEnrollNonLIS = sum(enrollmentNonLIS, na.rm = TRUE),
    shareNonLIS = enrollmentNonLIS / stateYrEnrollNonLIS,
    lnSNonLIS = safe_log(shareNonLIS),
    enrollmentNonLISimpute = enrollment - enrollmentLISimpute,
    stateYrEnrollNonLISimpute = sum(enrollmentNonLISimpute, na.rm = TRUE),
    shareNonLISimpute = enrollmentNonLISimpute / stateYrEnrollNonLISimpute,
    lnS_std = safe_log(shareNonLISimpute)
  ) %>%
  ungroup()

# -----------------------------------------------------------------------------
# PART 3A: Tables and Figures
# -----------------------------------------------------------------------------

main <- main %>% mutate(EBene = ifelse(benefit == "E", 1L, 0L))

# Table 1 descriptive statistics (export compact CSVs)
t1_premium <- main %>%
  filter(yearOfPlan == 1) %>%
  group_by(cohort) %>%
  summarise(mean = mean(premium, na.rm = TRUE), sd = sd(premium, na.rm = TRUE), N = sum(!is.na(premium)), .groups = "drop")
write_csv(t1_premium, "Analysis_output/Table1_premium.csv")

t1_deduct <- main %>%
  filter(yearOfPlan == 1) %>%
  group_by(cohort) %>%
  summarise(mean = mean(deductible, na.rm = TRUE), sd = sd(deductible, na.rm = TRUE), .groups = "drop")
write_csv(t1_deduct, "Analysis_output/Table1_deductible.csv")

t1_ebene <- main %>%
  filter(yearOfPlan == 1) %>%
  group_by(cohort) %>%
  summarise(mean = mean(EBene, na.rm = TRUE), sd = sd(EBene, na.rm = TRUE), .groups = "drop")
write_csv(t1_ebene, "Analysis_output/Table1_EBene.csv")

# Figure 1: kernel density
fig1dat <- main %>%
  filter(year == 2010, cohort <= 2007, benefit == "B") %>%
  transmute(premium, group = "2006-7 Cohorts") %>%
  bind_rows(
    main %>% filter(year == 2010, cohort >= 2008, benefit == "B") %>% transmute(premium, group = "2008+ Cohorts")
  )

ggplot(fig1dat, aes(x = premium, linetype = group)) +
  geom_density(na.rm = TRUE) +
  labs(x = "Annual Premium", y = "Density", linetype = NULL) +
  theme_minimal()
ggsave("Analysis_output/Figure1.png", width = 7, height = 5)

# Table 2: Response of Enrollment to Past Prices
L0BA_vars <- grep("^L0BA_", names(main), value = TRUE)
L1BA_vars <- grep("^L1BA_", names(main), value = TRUE)
L0BA_rhs <- paste(L0BA_vars, collapse = " + ")
L1BA_rhs <- paste(L1BA_vars, collapse = " + ")

ifCondit <- with(main, cohort == 2006 & year == 2007 & maxYear >= 2007 & benefit == "B" & minIsBasic2007 == 1)
ifConditAlt <- with(main, cohort == 2006 & year == 2006 & maxYear >= 2007 & benefit == "B" & minIsBasic2007 == 1)

f_t2_2 <- as.formula(paste0("lnS_std ~ premium + LIS + factor(btypedetail) + ", L0BA_rhs, " | state"))
f_t2_3 <- as.formula(paste0("lnS_std ~ premium + LIS + factor(btypedetail) + ", L0BA_rhs, " | state"))
f_t2_1 <- as.formula(paste0("lnS_std ~ premium + L1premium + LIS + L1LIS + factor(btypedetail) + ", L0BA_rhs,
                            " + factor(L1btypedetail) + ", L1BA_rhs, " | state"))

T2_2 <- feols(f_t2_2, data = main[ifCondit, ], vcov = ~ firmID)
main <- add_define_sample(main, T2_2)
T2_3 <- feols(f_t2_3, data = main[ifConditAlt & main$inLastSample == 1, ], vcov = ~ firmID)
T2_1 <- feols(f_t2_1, data = main[ifCondit, ], vcov = ~ firmID)

f_t2_5 <- update(f_t2_2, . ~ . | state + firmID)
f_t2_6 <- update(f_t2_3, . ~ . | state + firmID)
f_t2_4 <- update(f_t2_1, . ~ . | state + firmID)
T2_5 <- feols(f_t2_5, data = main[ifCondit, ], vcov = ~ firmID)
main <- add_define_sample(main, T2_5)
T2_6 <- feols(f_t2_6, data = main[ifConditAlt & main$inLastSample == 1, ], vcov = ~ firmID)
T2_4 <- feols(f_t2_4, data = main[ifCondit, ], vcov = ~ firmID)

write_model_table(list(T2_1 = T2_1, T2_2 = T2_2, T2_3 = T2_3, T2_4 = T2_4, T2_5 = T2_5, T2_6 = T2_6),
                  "Analysis_output/Table2.html")

# Figure 2: PDP enrollment by cohort
fig2 <- main %>%
  mutate(n = 1L,
         enrollmentNonLISimpute = enrollment - enrollmentLISimpute) %>%
  group_by(cohort, year) %>%
  summarise(enrollment = sum(enrollment, na.rm = TRUE),
            n = sum(n),
            enrollmentLIS = sum(enrollmentLIS, na.rm = TRUE),
            enrollmentNonLISimpute = sum(enrollmentNonLISimpute, na.rm = TRUE),
            .groups = "drop") %>%
  mutate(enrollmentThousands = enrollment / 1000,
         enrollmentLISThousands = ifelse(year == 2010, NA_real_, enrollmentLIS / 1000),
         enrollmentNonLISimputeThousands = ifelse(year == 2010, NA_real_, enrollmentNonLISimpute / 1000))

ggplot(fig2, aes(x = year, y = enrollmentThousands, group = factor(cohort))) +
  geom_line() +
  geom_point(data = subset(fig2, cohort == 2010)) +
  labs(x = "Year", y = "Enrollment (Thousands)") +
  theme_minimal() +
  theme(legend.position = "none")
ggsave("Analysis_output/Figure2.png", width = 7, height = 5)

# Table 4
main <- main %>% mutate(enrollInK = enrollment / 1000)
Dyear_vars <- grep("^Dyear", names(main), value = TRUE)
DOfPlan_vars <- grep("^(DOfPlan|_DOfPlan1)", names(main), value = TRUE)
BAcDeduct_vars <- grep("^BAcDeduct", names(main), value = TRUE)
Dyear_rhs <- paste(Dyear_vars, collapse = " + ")
DOfPlan_rhs <- paste(DOfPlan_vars, collapse = " + ")
BA_rhs <- paste(BAcDeduct_vars, collapse = " + ")
yearDedInt_rhs <- paste0("factor(btypedetail)^factor(year)", ifelse(length(BAcDeduct_vars) > 0, paste0(" + ", BA_rhs), ""))

R1 <- feols(as.formula(paste0("lnPremium ~ ", Dyear_rhs, " + ", DOfPlan_rhs, " | state^year")),
            data = filter(main, benefit == "B"), vcov = ~ firmID)
R2 <- feols(as.formula(paste0("lnPremium ~ ", DOfPlan_rhs, " + MAPlan + ", yearDedInt_rhs, " | state^year")),
            data = filter(main, benefit == "B"), vcov = ~ firmID)
R3 <- feols(as.formula(paste0("lnPremium ~ ", DOfPlan_rhs, " + ", yearDedInt_rhs, " | firmID + state^year")),
            data = filter(main, benefit == "B"), vcov = ~ firmID)
R4 <- feols(as.formula(paste0("lnPremium ~ ", Dyear_rhs, " + ", DOfPlan_rhs, " | state^year")),
            data = filter(main, benefit == "B"), weights = ~ enrollInK, vcov = ~ firmID)
R5 <- feols(as.formula(paste0("lnPremium ~ ", DOfPlan_rhs, " + MAPlan + ", yearDedInt_rhs, " | state^year")),
            data = filter(main, benefit == "B"), weights = ~ enrollInK, vcov = ~ firmID)
R6 <- feols(as.formula(paste0("lnPremium ~ ", DOfPlan_rhs, " + ", yearDedInt_rhs, " | firmID + state^year")),
            data = filter(main, benefit == "B"), weights = ~ enrollInK, vcov = ~ firmID)

write_model_table(list(R1 = R1, R2 = R2, R3 = R3, R4 = R4, R5 = R5, R6 = R6),
                  "Analysis_output/Table4.html")

# Figure 5: Premiums by cohort
fig5 <- main %>%
  filter(benefit == "B") %>%
  group_by(cohort, year) %>%
  summarise(premium = mean(premium, na.rm = TRUE),
            sd = sd(premium, na.rm = TRUE),
            n = sum(!is.na(premium)), .groups = "drop") %>%
  mutate(hiStdErr = premium + sd / sqrt(n),
         loStdErr = premium - sd / sqrt(n))

ggplot(fig5, aes(x = year, y = premium, group = factor(cohort))) +
  geom_errorbar(aes(ymin = loStdErr, ymax = hiStdErr), width = 0.1, color = "grey50") +
  geom_line(color = "black") +
  geom_point(shape = 4, color = "black") +
  labs(x = "Year", y = "Monthly Premium ($)") +
  theme_minimal() +
  theme(legend.position = "none")
ggsave("Analysis_output/Figure5.png", width = 7, height = 5)

# -----------------------------------------------------------------------------
# PART 3B: RD preparation
# -----------------------------------------------------------------------------

main <- main %>%
  left_join(subsidies, by = c("PDPregion", "year")) %>%
  rename(LISsubsidy = s) %>%
  mutate(
    LISPremium = premium - LISsubsidy,
    proposedBenchmarkPlan = ifelse(LISPremium <= 0, 1L, 0L),
    ProblemObs = case_when(
      LISPremium < 0 & LIS == 0 ~ 1L,
      LISPremium > 0 & LIS == 1 ~ 2L,
      TRUE ~ NA_integer_
    )
  )

main <- main %>%
  mutate(
    LISPremium = ifelse(benefit == "E", NA_real_, LISPremium),
    proposedBenchmarkPlan = ifelse(benefit == "E", NA_integer_, proposedBenchmarkPlan),
    LISPremiumSq = LISPremium^2,
    LISPremiumCub = LISPremium^3,
    LISPremiumQuart = LISPremium^4,
    LISPremiumSq_IS = LISPremium^2 * LIS,
    LISPremiumCub_IS = LISPremium^3 * LIS,
    LISPremiumQuart_IS = LISPremium^4 * LIS,
    premiumSq = premium^2,
    premiumCub = premium^3,
    premiumQuart = premium^4,
    LISPremiumNeg = ifelse(LISPremium <= 0, LISPremium, 0),
    LISPremiumPos = ifelse(LISPremium >= 0, LISPremium, 0),
    LISPremiumNegSq = LISPremiumNeg^2,
    LISPremiumNegCub = LISPremiumNeg^3,
    LISPremiumNegQuart = LISPremiumNeg^4,
    LISPremiumPosSq = LISPremiumPos^2,
    LISPremiumPosCub = LISPremiumPos^3,
    LISPremiumPosQuart = LISPremiumPos^4
  )

main <- main %>% arrange(uniqueIDNum, year) %>% group_by(uniqueIDNum)
for (x in 1:4) {
  for (v in c("LISPremium", "LISPremiumNeg", "LISPremiumPos",
              "LISPremiumNegSq", "LISPremiumNegCub", "LISPremiumNegQuart",
              "LISPremiumPosSq", "LISPremiumPosCub", "LISPremiumPosQuart")) {
    main[[paste0("L", x, v)]] <- lag_by_group(main[[v]], x)
  }
}
main <- ungroup(main)

for (x in 2006:2009) {
  main[[paste0("attritBy", x)]] <- ifelse(main$maxYear <= x, 1L, 0L)
}

main <- main %>% arrange(uniqueIDNum, year) %>% group_by(uniqueIDNum) %>%
  mutate(
    alwaysLIS07 = as.integer(LIS == 1 & L1LIS == 1 & year == 2007),
    alwaysLIS08 = as.integer(LIS == 1 & L1LIS == 1 & L2LIS == 1 & year == 2008),
    alwaysLIS09 = as.integer(LIS == 1 & L1LIS == 1 & L2LIS == 1 & L3LIS == 1 & year == 2009),
    alwaysLIS10 = as.integer(LIS == 1 & L1LIS == 1 & L2LIS == 1 & L3LIS == 1 & L4LIS == 1 & year == 2010),
    neverLIS07 = as.integer(LIS == 0 & year == 2007),
    neverLIS08 = as.integer(LIS == 0 & L1LIS == 0 & year == 2008),
    neverLIS09 = as.integer(LIS == 0 & L1LIS == 0 & L2LIS == 0 & year == 2009),
    neverLIS10 = as.integer(LIS == 0 & L1LIS == 0 & L2LIS == 0 & L3LIS == 0 & year == 2010)
  ) %>%
  ungroup()

# RD windows
main <- main %>% mutate(
  RDwindow = as.integer(LISPremium >= -10 & LISPremium <= 10),
  belowBench = ifelse(RDwindow == 1 & LISPremium <= 0, 1L, ifelse(RDwindow == 1 & LISPremium > 0, 0L, NA_integer_))
)

make_window_vars <- function(data, x, lower, upper) {
  rd <- as.integer(data$LISPremium >= lower & data$LISPremium <= upper)
  below <- ifelse(rd == 1 & data$LISPremium <= 0, 1L, ifelse(rd == 1 & data$LISPremium > 0, 0L, NA_integer_))
  data[[paste0("RDwindow", x)]] <- rd
  data[[paste0("belowBench", x)]] <- below
  data[[paste0("belowBench2006Temp", x)]] <- ifelse(below == 1 & data$year == 2006, 1L, 0L)
  data[[paste0("RDwindow2006Temp", x)]] <- ifelse(rd == 1 & data$year == 2006, 1L, 0L)
  data %>%
    group_by(uniqueID) %>%
    mutate(
      !!paste0("belowBench2006", x) := max(.data[[paste0("belowBench2006Temp", x)]], na.rm = TRUE),
      !!paste0("RDwindow2006", x) := max(.data[[paste0("RDwindow2006Temp", x)]], na.rm = TRUE)
    ) %>%
    ungroup()
}

main <- main %>%
  mutate(
    belowBench2006Temp = ifelse(belowBench == 1 & year == 2006, 1L, 0L),
    RDwindow2006Temp = ifelse(RDwindow == 1 & year == 2006, 1L, 0L),
    LISsubsidy2006Temp = ifelse(year == 2006, LISsubsidy, 0)
  ) %>%
  group_by(uniqueID) %>%
  mutate(
    belowBench2006 = max(belowBench2006Temp, na.rm = TRUE),
    RDwindow2006 = max(RDwindow2006Temp, na.rm = TRUE),
    LISsubsidy2006 = max(LISsubsidy2006Temp, na.rm = TRUE)
  ) %>%
  ungroup()

main <- make_window_vars(main, 2, -4, 4)
main <- make_window_vars(main, 3, -2.5, 2.5)
main <- make_window_vars(main, 4, -6, 6)
main$RDwindow20061 <- main$RDwindow2006

main <- main %>% mutate(
  bench0607 = as.integer(belowBench2006 == 1 & LIS == 1 & year == 2007),
  bench06Not07 = as.integer(belowBench2006 == 1 & LIS == 0 & year == 2007),
  benchNot06Yes07 = as.integer(belowBench2006 == 0 & LIS == 1 & year == 2007)
)
for (yr in 2007:2010) {
  main[[paste0("bench06", yr)]] <- as.integer(main$belowBench2006 == 1 & main$LIS == 1 & main$year == yr)
  main[[paste0("bench06Not", yr)]] <- as.integer(main$belowBench2006 == 1 & main$LIS == 0 & main$year == yr)
  main[[paste0("benchNot06Yes", yr)]] <- as.integer(main$belowBench2006 == 0 & main$LIS == 1 & main$year == yr)
}

# -----------------------------------------------------------------------------
# PART 3C: RD tables and figures
# -----------------------------------------------------------------------------

x <- 2
rd_models_A <- list(
  iS10Lin2 = feols(lnS ~ belowBench2006 + L4LISPremiumNeg + L4LISPremiumPos,
                   data = subset(main, year == 2010 & RDwindow20062 == 1), vcov = ~ firmID),
  iS09Lin2 = feols(lnS ~ belowBench2006 + L3LISPremiumNeg + L3LISPremiumPos,
                   data = subset(main, year == 2009 & RDwindow20062 == 1), vcov = ~ firmID),
  iS08Lin2 = feols(lnS ~ belowBench2006 + L2LISPremiumNeg + L2LISPremiumPos,
                   data = subset(main, year == 2008 & RDwindow20062 == 1), vcov = ~ firmID),
  iS07Lin2 = feols(lnS ~ belowBench2006 + L1LISPremiumNeg + L1LISPremiumPos,
                   data = subset(main, year == 2007 & RDwindow20062 == 1), vcov = ~ firmID),
  iS06Lin2 = feols(lnS ~ belowBench2006 + LISPremiumNeg + LISPremiumPos,
                   data = subset(main, year == 2006 & RDwindow20062 == 1), vcov = ~ firmID)
)

rd_models_B <- list(
  iS10Opt2 = feols(as.formula(paste0("lnS ~ belowBench2006 + L4LISPremiumNeg + L4LISPremiumPos + L4LISPremiumNegSq + L4LISPremiumPosSq + ",
                                     paste(grep("^L4BA_", names(main), value = TRUE), collapse = " + "),
                                     " + factor(L4btypedetail) | state + firmID")),
                    data = subset(main, year == 2010 & RDwindow20062 == 1), vcov = ~ firmID),
  iS09Opt2 = feols(as.formula(paste0("lnS ~ belowBench2006 + L3LISPremiumNeg + L3LISPremiumPos + L3LISPremiumNegSq + L3LISPremiumPosSq + ",
                                     paste(grep("^L3BA_", names(main), value = TRUE), collapse = " + "),
                                     " + factor(L3btypedetail) | state + firmID")),
                    data = subset(main, year == 2009 & RDwindow20062 == 1), vcov = ~ firmID),
  iS08Opt2 = feols(as.formula(paste0("lnS ~ belowBench2006 + L2LISPremiumNeg + L2LISPremiumPos + L2LISPremiumNegSq + L2LISPremiumPosSq + ",
                                     paste(grep("^L2BA_", names(main), value = TRUE), collapse = " + "),
                                     " + factor(L2btypedetail) | state + firmID")),
                    data = subset(main, year == 2008 & RDwindow20062 == 1), vcov = ~ firmID),
  iS07Opt2 = feols(as.formula(paste0("lnS ~ belowBench2006 + L1LISPremiumNeg + L1LISPremiumPos + L1LISPremiumNegSq + L1LISPremiumPosSq + ",
                                     paste(grep("^L1BA_", names(main), value = TRUE), collapse = " + "),
                                     " + factor(L1btypedetail) | state + firmID")),
                    data = subset(main, year == 2007 & RDwindow20062 == 1), vcov = ~ firmID),
  iS06Opt2 = feols(as.formula(paste0("lnS ~ belowBench2006 + LISPremiumNeg + LISPremiumPos + LISPremiumNegSq + LISPremiumPosSq + ",
                                     paste(grep("^L0BA_", names(main), value = TRUE), collapse = " + "),
                                     " + factor(L0btypedetail) | state + firmID")),
                    data = subset(main, year == 2006 & RDwindow20062 == 1), vcov = ~ firmID)
)

intSLin2 <- list(
  intSLin102 = feols(lnS ~ bench062010 + bench06Not2010 + benchNot06Yes2010 + L4LISPremiumNeg + L4LISPremiumPos,
                     data = subset(main, year == 2010 & RDwindow20062 == 1), vcov = ~ firmID),
  intSLin092 = feols(lnS ~ bench062009 + bench06Not2009 + benchNot06Yes2009 + L3LISPremiumNeg + L3LISPremiumPos,
                     data = subset(main, year == 2009 & RDwindow20062 == 1), vcov = ~ firmID),
  intSLin082 = feols(lnS ~ bench062008 + bench06Not2008 + benchNot06Yes2008 + L2LISPremiumNeg + L2LISPremiumPos,
                     data = subset(main, year == 2008 & RDwindow20062 == 1), vcov = ~ firmID),
  intSLin072 = feols(lnS ~ bench062007 + bench06Not2007 + benchNot06Yes2007 + L1LISPremiumNeg + L1LISPremiumPos,
                     data = subset(main, year == 2007 & RDwindow20062 == 1), vcov = ~ firmID)
)

write_model_table(rd_models_A, "Analysis_output/Table3-PanelA.html")
write_model_table(rd_models_B, "Analysis_output/Table3-PanelB.html")
write_model_table(intSLin2, "Analysis_output/Table3-PanelC.html")

# Figure 3 bins and fitted values
nBinOver2 <- 20
h <- 10
step <- h / nBinOver2

main <- main %>%
  mutate(theBinAlTemp = case_when(
    year == 2006 & LISPremium >= -step * 1 & LISPremium < 0 ~ ceiling(LISPremium / step) * step,
    year == 2006 & LISPremium >= step & LISPremium < step * (nBinOver2 + 1) ~ floor(LISPremium / step) * step,
    TRUE ~ NA_real_
  )) %>%
  group_by(uniqueID) %>%
  mutate(theBinAl = max(theBinAlTemp, na.rm = TRUE)) %>%
  ungroup()
main$theBinAl[!is.finite(main$theBinAl)] <- NA

year <- 2006
P <- ""
ScatWin <- 1
RegWin <- 2
PolyWin <- 1

m_bin <- feols(lnS ~ factor(theBinAl), data = subset(main, year == year & RDwindow20061 == 1 & benefit == "B"), vcov = ~ firmID)
main$lnSHat <- NA_real_
main$lnSHat[main$year == year] <- predict(m_bin, newdata = subset(main, year == year))

m_lin <- feols(lnS ~ belowBench2006 + LISPremiumNeg + LISPremiumPos,
               data = subset(main, year == year & RDwindow20062 == 1 & benefit == "B"), vcov = ~ firmID)
main$lnSHatAlt <- NA_real_
main$lnSHatAlt[main$year == year] <- predict(m_lin, newdata = subset(main, year == year))

m_poly <- feols(lnS ~ belowBench2006 + LISPremiumNeg + LISPremiumPos + LISPremiumNegSq + LISPremiumPosSq + LISPremiumNegCub + LISPremiumPosCub + LISPremiumNegQuart + LISPremiumPosQuart,
                data = subset(main, year == year & RDwindow20061 == 1 & benefit == "B"), vcov = ~ firmID)
main$lnSHatAltPoly <- NA_real_
main$lnSHatAltPoly[main$year == year] <- predict(m_poly, newdata = subset(main, year == year))

fig3 <- subset(main, year == 2006 & benefit == "B")
ggplot() +
  geom_point(data = subset(fig3, RDwindow20061 == 1), aes(x = theBinAl, y = lnSHat)) +
  geom_line(data = subset(fig3, RDwindow20062 == 1), aes(x = LISPremium, y = lnSHatAlt), linetype = "dashed", color = "grey50") +
  geom_line(data = subset(fig3, RDwindow20061 == 1), aes(x = LISPremium, y = lnSHatAltPoly), color = "black") +
  labs(x = "Monthly Premium - LIS Subsidy, 2006", y = "Log Enrollment Share, 2006") +
  theme_minimal()
ggsave("Analysis_output/Figure3.png", width = 7, height = 5)

# Figure 4: LIS Premiums in 2007 as function of 2006 running variable
m4_bin <- feols(LISPremium ~ factor(theBinAl), data = subset(main, year == 2007 & RDwindow20061 == 1 & L1benefit == "B"), vcov = ~ firmID)
main$binHat <- NA_real_
main$binHat[main$year == 2007] <- predict(m4_bin, newdata = subset(main, year == 2007))

m4_lin <- feols(LISPremium ~ belowBench2006 + L1LISPremiumNeg + L1LISPremiumPos,
                data = subset(main, year == 2007 & RDwindow20064 == 1 & L1benefit == "B"), vcov = ~ firmID)
main$linearHat <- NA_real_
main$linearHat[main$year == 2007] <- predict(m4_lin, newdata = subset(main, year == 2007))

m4_poly <- feols(LISPremium ~ belowBench2006 + L1LISPremiumNeg + L1LISPremiumPos + L1LISPremiumNegSq + L1LISPremiumPosSq + L1LISPremiumNegCub + L1LISPremiumPosCub,
                 data = subset(main, year == 2007 & RDwindow20061 == 1 & L1benefit == "B"), vcov = ~ firmID)
main$polyHat <- NA_real_
main$polyHat[main$year == 2007] <- predict(m4_poly, newdata = subset(main, year == 2007))

fig4 <- subset(main, year == 2007 & L1benefit == "B")
ggplot() +
  geom_point(data = subset(fig4, RDwindow20061 == 1), aes(x = theBinAl, y = binHat)) +
  geom_line(data = subset(fig4, RDwindow20064 == 1), aes(x = L1LISPremium, y = linearHat), linetype = "dashed", color = "grey50") +
  geom_line(data = subset(fig4, RDwindow20061 == 1), aes(x = L1LISPremium, y = polyHat), color = "black") +
  labs(x = "Monthly Premium - LIS Subsidy, 2006", y = "Monthly Premiums - LIS Subsidy, 2007") +
  theme_minimal()
ggsave("Analysis_output/Figure4.png", width = 7, height = 5)

message("R translation complete. Outputs written to Analysis_output/.")
