import ProductInvariants.Certified.PolynomialIntegral

/-!
# High-precision certified enclosures of `Lambda`

This module isolates the computationally heavy certificate theorems for the
prime product-integral constant `Lambda`: the `N = 503, 1009, 2003` sandwich
bounds.

These are the only `native_decide` calls in the certificate layer whose runtime
is significant. They evaluate `primePhaseIntegralRat N =
Integral_{0..1} Product_{p prime, p <= N} (1-u^p) du` as an exact rational.
The reusable sandwich machinery and the cheap `N <= 101` certificates remain in
`ProductInvariants.Certified.PolynomialIntegral`.
-/

namespace ProductInvariants.Certified

open MeasureTheory intervalIntegral Polynomial

set_option maxRecDepth 100000

theorem sandwichLowerRat_503_505_le_Lambda :
    (sandwichLowerRat 503 505 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 503) (m := 505) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge_504 : 504 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge_504 with hp504 | hp504
  · exact Nat.succ_le_of_lt hp504
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 504) hp_prime

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_503_lt :
    primePhaseIntegralRat 503 <
      (5506530112728432344854780 : ℚ) / 10000000000000000000000000 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_503_505_gt :
    (5506530112728420906200021 : ℚ) / 10000000000000000000000000 <
      sandwichLowerRat 503 505 := by
  native_decide

theorem Lambda_gt_5506530112728420906200021_div_1e25 :
    (5506530112728420906200021 : ℝ) / 10000000000000000000000000 < Lambda := by
  have hrat :
      ((5506530112728420906200021 : ℚ) / 10000000000000000000000000 : ℝ) <
        (sandwichLowerRat 503 505 : ℝ) := by
    exact_mod_cast sandwichLowerRat_503_505_gt
  norm_num at hrat ⊢
  exact hrat.trans_le sandwichLowerRat_503_505_le_Lambda

theorem Lambda_lt_5506530112728432344854780_div_1e25 :
    Lambda < (5506530112728432344854780 : ℝ) /
      10000000000000000000000000 := by
  have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 503) :=
    Lambda_le_prime_truncation 503
  rw [phaseIntegral_primeSetUpTo_eq_rat] at hΛ
  have hrat : (primePhaseIntegralRat 503 : ℝ) <
      ((5506530112728432344854780 : ℚ) / 10000000000000000000000000 : ℝ) := by
    exact_mod_cast primePhaseIntegralRat_503_lt
  norm_num at hrat ⊢
  exact lt_of_le_of_lt hΛ hrat

theorem Lambda_bounds_503 :
    (5506530112728420906200021 : ℝ) / 10000000000000000000000000 < Lambda ∧
      Lambda < (5506530112728432344854780 : ℝ) /
        10000000000000000000000000 :=
  ⟨Lambda_gt_5506530112728420906200021_div_1e25,
    Lambda_lt_5506530112728432344854780_div_1e25⟩

theorem sandwichLowerRat_1009_1011_le_Lambda :
    (sandwichLowerRat 1009 1011 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 1009) (m := 1011) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge_1010 : 1010 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge_1010 with hp1010 | hp1010
  · exact Nat.succ_le_of_lt hp1010
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 1010) hp_prime

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_1009_lt :
    primePhaseIntegralRat 1009 <
      (550653011272842963579465933094387203471136467695308801315764 : ℚ) / 10 ^ 60 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_1009_1011_gt :
    (550653011272842963574907227315784759883099490122684597014105 : ℚ) / 10 ^ 60 <
      sandwichLowerRat 1009 1011 := by
  native_decide

theorem Lambda_gt_550653011272842963574907227315784759883099490122684597014105_div_1e60 :
    (550653011272842963574907227315784759883099490122684597014105 : ℝ) / 10 ^ 60 <
      Lambda := by
  have hrat :
      ((550653011272842963574907227315784759883099490122684597014105 : ℚ) / 10 ^ 60 : ℝ) <
        (sandwichLowerRat 1009 1011 : ℝ) := by
    exact_mod_cast sandwichLowerRat_1009_1011_gt
  norm_num at hrat ⊢
  exact hrat.trans_le sandwichLowerRat_1009_1011_le_Lambda

theorem Lambda_lt_550653011272842963579465933094387203471136467695308801315764_div_1e60 :
    Lambda <
      (550653011272842963579465933094387203471136467695308801315764 : ℝ) / 10 ^ 60 := by
  have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 1009) :=
    Lambda_le_prime_truncation 1009
  rw [phaseIntegral_primeSetUpTo_eq_rat] at hΛ
  have hrat : (primePhaseIntegralRat 1009 : ℝ) <
      ((550653011272842963579465933094387203471136467695308801315764 : ℚ) / 10 ^ 60 : ℝ) := by
    exact_mod_cast primePhaseIntegralRat_1009_lt
  norm_num at hrat ⊢
  exact lt_of_le_of_lt hΛ hrat

theorem Lambda_bounds_1009 :
    (550653011272842963574907227315784759883099490122684597014105 : ℝ) / 10 ^ 60 <
      Lambda ∧
    Lambda <
      (550653011272842963579465933094387203471136467695308801315764 : ℝ) / 10 ^ 60 :=
  ⟨Lambda_gt_550653011272842963574907227315784759883099490122684597014105_div_1e60,
    Lambda_lt_550653011272842963579465933094387203471136467695308801315764_div_1e60⟩

theorem sandwichLowerRat_2003_2005_le_Lambda :
    (sandwichLowerRat 2003 2005 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 2003) (m := 2005) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge_2004 : 2004 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge_2004 with hp2004 | hp2004
  · exact Nat.succ_le_of_lt hp2004
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 2004) hp_prime

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_2003_lt :
    primePhaseIntegralRat 2003 <
      (550653011272842963577971757142083257920591723109550420057790 : ℚ) / 10 ^ 60 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_2003_2005_gt :
    (550653011272842963577971756854046512125342959043141558898004 : ℚ) / 10 ^ 60 <
      sandwichLowerRat 2003 2005 := by
  native_decide

theorem Lambda_gt_550653011272842963577971756854046512125342959043141558898004_div_1e60 :
    (550653011272842963577971756854046512125342959043141558898004 : ℝ) / 10 ^ 60 <
      Lambda := by
  have hrat :
      ((550653011272842963577971756854046512125342959043141558898004 : ℚ) / 10 ^ 60 : ℝ) <
        (sandwichLowerRat 2003 2005 : ℝ) := by
    exact_mod_cast sandwichLowerRat_2003_2005_gt
  norm_num at hrat ⊢
  exact hrat.trans_le sandwichLowerRat_2003_2005_le_Lambda

theorem Lambda_lt_550653011272842963577971757142083257920591723109550420057790_div_1e60 :
    Lambda <
      (550653011272842963577971757142083257920591723109550420057790 : ℝ) / 10 ^ 60 := by
  have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 2003) :=
    Lambda_le_prime_truncation 2003
  rw [phaseIntegral_primeSetUpTo_eq_rat] at hΛ
  have hrat : (primePhaseIntegralRat 2003 : ℝ) <
      ((550653011272842963577971757142083257920591723109550420057790 : ℚ) / 10 ^ 60 : ℝ) := by
    exact_mod_cast primePhaseIntegralRat_2003_lt
  norm_num at hrat ⊢
  exact lt_of_le_of_lt hΛ hrat

theorem Lambda_bounds_2003 :
    (550653011272842963577971756854046512125342959043141558898004 : ℝ) / 10 ^ 60 <
      Lambda ∧
    Lambda <
      (550653011272842963577971757142083257920591723109550420057790 : ℝ) / 10 ^ 60 :=
  ⟨Lambda_gt_550653011272842963577971756854046512125342959043141558898004_div_1e60,
    Lambda_lt_550653011272842963577971757142083257920591723109550420057790_div_1e60⟩

end ProductInvariants.Certified
