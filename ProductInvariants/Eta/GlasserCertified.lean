import ProductInvariants.Eta.ClosedForms
import LeanCert

set_option linter.style.nativeDecide false

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace ProductInvariants

/-!
# LeanCert certificates for Glasser integer-shift values

This file records small LeanCert certificates for the hyperbolic right-hand side
of Glasser's eta-integral formula at the integer-shift parameters
`y = k + 23 / 24`, for `k = 0, 1, 2`.

For these parameters, writing `d = 24k + 23`, the closed form in
`glasserRHSIntegerShift` is

`π * sqrt (scale / d) * sinh (π * sqrt d / 3) / cosh (π * sqrt d / 2)`.

LeanCert certifies the equivalent cross-multiplied inequalities, avoiding any
division inside the interval expression:

`c * cosh (π * sqrt d / 2) * sqrt d ≤ π * sqrt scale * sinh (π * sqrt d / 3)`.
-/

/-- The one-point interval used for closed numerical expressions. -/
def glasserPointInterval : IntervalRat := ⟨0, 0, by norm_num⟩

private def q (n d : Int) : Expr := Expr.const (Rat.divInt n d)
private def piE : Expr := Expr.namedConst MathConst.pi
private def sqrtE (e : Expr) : Expr := Expr.sqrt e
private def sinhE (e : Expr) : Expr := Expr.sinh e
private def coshE (e : Expr) : Expr := Expr.cosh e
private def addE (a b : Expr) : Expr := Expr.add a b
private def mulE (a b : Expr) : Expr := Expr.mul a b
private def negE (a : Expr) : Expr := Expr.neg a
private def subE (a b : Expr) : Expr := addE a (negE b)

private def glasserNumeratorCrossE (scale d : Int) : Expr :=
  mulE (mulE piE (sqrtE (q scale 1)))
    (sinhE (mulE piE (mulE (sqrtE (q d 1)) (q 1 3))))

private def glasserDenominatorScaledE (d : Int) : Expr :=
  mulE (coshE (mulE piE (mulE (sqrtE (q d 1)) (q 1 2))))
    (sqrtE (q d 1))

private def glasserLowerCrossE (scale d n den : Int) : Expr :=
  subE (glasserNumeratorCrossE scale d) (mulE (q n den) (glasserDenominatorScaledE d))

private def glasserUpperCrossE (scale d n den : Int) : Expr :=
  subE (glasserNumeratorCrossE scale d) (mulE (q n den) (glasserDenominatorScaledE d))

private theorem glasserLowerCrossE_supported (scale d n den : Int) :
    ExprSupportedCore (glasserLowerCrossE scale d n den) := by
  unfold glasserLowerCrossE glasserNumeratorCrossE glasserDenominatorScaledE
    subE addE negE mulE sinhE coshE sqrtE piE q
  repeat constructor

private theorem glasserUpperCrossE_supported (scale d n den : Int) :
    ExprSupportedCore (glasserUpperCrossE scale d n den) := by
  unfold glasserUpperCrossE glasserNumeratorCrossE glasserDenominatorScaledE
    subE addE negE mulE sinhE coshE sqrtE piE q
  repeat constructor

/--
LeanCert lower certificate for `k = 0`, i.e. `d = 23`.

This proves the cross-multiplied form of
`0.36 ≤ glasserRHSIntegerShift 0`.
-/
theorem glasserRHSIntegerShift0_lower_cross_cert :
    ∀ x ∈ glasserPointInterval,
      (0 : ℚ) ≤ Expr.eval (fun _ => x) (glasserLowerCrossE 48 23 36 100) :=
  verify_lower_bound (glasserLowerCrossE 48 23 36 100)
    (glasserLowerCrossE_supported 48 23 36 100)
    glasserPointInterval 0 { taylorDepth := 80 } (by native_decide)

/--
LeanCert upper certificate for `k = 0`, i.e. `d = 23`.

This proves the cross-multiplied form of
`glasserRHSIntegerShift 0 ≤ 0.37`.
-/
theorem glasserRHSIntegerShift0_upper_cross_cert :
    ∀ x ∈ glasserPointInterval,
      Expr.eval (fun _ => x) (glasserUpperCrossE 48 23 37 100) ≤ (0 : ℚ) :=
  verify_upper_bound (glasserUpperCrossE 48 23 37 100)
    (glasserUpperCrossE_supported 48 23 37 100)
    glasserPointInterval 0 { taylorDepth := 80 } (by native_decide)

/--
LeanCert lower certificate for `k = 1`, i.e. `d = 47`.

This proves the cross-multiplied form of
`0.08 ≤ glasserRHSIntegerShift 1`.
-/
theorem glasserRHSIntegerShift1_lower_cross_cert :
    ∀ x ∈ glasserPointInterval,
      (0 : ℚ) ≤ Expr.eval (fun _ => x) (glasserLowerCrossE 48 47 8 100) :=
  verify_lower_bound (glasserLowerCrossE 48 47 8 100)
    (glasserLowerCrossE_supported 48 47 8 100)
    glasserPointInterval 0 { taylorDepth := 80 } (by native_decide)

/--
LeanCert upper certificate for `k = 1`, i.e. `d = 47`.

This proves the cross-multiplied form of
`glasserRHSIntegerShift 1 ≤ 0.09`.
-/
theorem glasserRHSIntegerShift1_upper_cross_cert :
    ∀ x ∈ glasserPointInterval,
      Expr.eval (fun _ => x) (glasserUpperCrossE 48 47 9 100) ≤ (0 : ℚ) :=
  verify_upper_bound (glasserUpperCrossE 48 47 9 100)
    (glasserUpperCrossE_supported 48 47 9 100)
    glasserPointInterval 0 { taylorDepth := 80 } (by native_decide)

/--
LeanCert lower certificate for `k = 2`, i.e. `d = 71`.

This proves the cross-multiplied form of
`0.03 ≤ glasserRHSIntegerShift 2`.
-/
theorem glasserRHSIntegerShift2_lower_cross_cert :
    ∀ x ∈ glasserPointInterval,
      (0 : ℚ) ≤ Expr.eval (fun _ => x) (glasserLowerCrossE 48 71 3 100) :=
  verify_lower_bound (glasserLowerCrossE 48 71 3 100)
    (glasserLowerCrossE_supported 48 71 3 100)
    glasserPointInterval 0 { taylorDepth := 80 } (by native_decide)

/--
LeanCert upper certificate for `k = 2`, i.e. `d = 71`.

This proves the cross-multiplied form of
`glasserRHSIntegerShift 2 ≤ 0.04`.
-/
theorem glasserRHSIntegerShift2_upper_cross_cert :
    ∀ x ∈ glasserPointInterval,
      Expr.eval (fun _ => x) (glasserUpperCrossE 48 71 4 100) ≤ (0 : ℚ) :=
  verify_upper_bound (glasserUpperCrossE 48 71 4 100)
    (glasserUpperCrossE_supported 48 71 4 100)
    glasserPointInterval 0 { taylorDepth := 80 } (by native_decide)

/-- LeanCert certificate for `0.57733 ≤ evenExponentClosedForm`. -/
theorem evenExponentClosedForm_lower_cross_cert :
    ∀ x ∈ glasserPointInterval,
      (0 : ℚ) ≤ Expr.eval (fun _ => x) (glasserLowerCrossE 12 11 57733 100000) :=
  verify_lower_bound (glasserLowerCrossE 12 11 57733 100000)
    (glasserLowerCrossE_supported 12 11 57733 100000)
    glasserPointInterval 0 { taylorDepth := 80 } (by native_decide)

/-- LeanCert certificate for `evenExponentClosedForm ≤ 0.57734`. -/
theorem evenExponentClosedForm_upper_cross_cert :
    ∀ x ∈ glasserPointInterval,
      Expr.eval (fun _ => x) (glasserUpperCrossE 12 11 57734 100000) ≤ (0 : ℚ) :=
  verify_upper_bound (glasserUpperCrossE 12 11 57734 100000)
    (glasserUpperCrossE_supported 12 11 57734 100000)
    glasserPointInterval 0 { taylorDepth := 80 } (by native_decide)

private theorem closedForm_bounds_of_cross
    {scale d loNum hiNum den : Int} (hscale : 0 < (scale : ℝ)) (hd : 0 < (d : ℝ))
    (hlo :
      ∀ x ∈ glasserPointInterval,
        (0 : ℚ) ≤ Expr.eval (fun _ => x) (glasserLowerCrossE scale d loNum den))
    (hhi :
      ∀ x ∈ glasserPointInterval,
        Expr.eval (fun _ => x) (glasserUpperCrossE scale d hiNum den) ≤ (0 : ℚ)) :
    ((Rat.divInt loNum den : ℚ) : ℝ) ≤
        Real.pi * Real.sqrt ((scale : ℝ) / d) *
          Real.sinh (Real.pi * Real.sqrt d / 3) /
            Real.cosh (Real.pi * Real.sqrt d / 2) ∧
      Real.pi * Real.sqrt ((scale : ℝ) / d) *
          Real.sinh (Real.pi * Real.sqrt d / 3) /
            Real.cosh (Real.pi * Real.sqrt d / 2) ≤
        ((Rat.divInt hiNum den : ℚ) : ℝ) := by
  have hlo0 := hlo 0 (by simp [glasserPointInterval])
  have hhi0 := hhi 0 (by simp [glasserPointInterval])
  unfold glasserLowerCrossE glasserNumeratorCrossE glasserDenominatorScaledE
    subE addE negE mulE sinhE coshE sqrtE piE q at hlo0
  unfold glasserUpperCrossE glasserNumeratorCrossE glasserDenominatorScaledE
    subE addE negE mulE sinhE coshE sqrtE piE q at hhi0
  simp only [Expr.eval] at hlo0 hhi0
  norm_num at hlo0 hhi0
  have hsqrtScale : 0 < Real.sqrt (scale : ℝ) := Real.sqrt_pos.2 hscale
  have hsqrtD : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd
  have hcosh : 0 < Real.cosh (Real.pi * Real.sqrt (d : ℝ) / 2) := Real.cosh_pos _
  have hsqrt_div :
      Real.sqrt ((scale : ℝ) / d) = Real.sqrt (scale : ℝ) / Real.sqrt (d : ℝ) := by
    rw [Real.sqrt_div (le_of_lt hscale)]
  constructor
  · have hcross :
        ((Rat.divInt loNum den : ℚ) : ℝ) *
            Real.cosh (Real.pi * Real.sqrt (d : ℝ) / 2) * Real.sqrt (d : ℝ) ≤
          Real.pi * Real.sqrt (scale : ℝ) *
            Real.sinh (Real.pi * Real.sqrt (d : ℝ) / 3) := by
      simpa [MathConst.toReal, Rat.divInt_eq_div, mul_assoc, div_eq_mul_inv] using hlo0
    apply (le_div_iff₀ hcosh).2
    rw [hsqrt_div]
    have hdiv :
        ((Rat.divInt loNum den : ℚ) : ℝ) *
            Real.cosh (Real.pi * Real.sqrt (d : ℝ) / 2) ≤
          (Real.pi * Real.sqrt (scale : ℝ) *
            Real.sinh (Real.pi * Real.sqrt (d : ℝ) / 3)) / Real.sqrt (d : ℝ) :=
      (le_div_iff₀ hsqrtD).2 hcross
    have heq :
        Real.pi * (Real.sqrt (scale : ℝ) / Real.sqrt (d : ℝ)) *
            Real.sinh (Real.pi * Real.sqrt (d : ℝ) / 3) =
          (Real.pi * Real.sqrt (scale : ℝ) *
            Real.sinh (Real.pi * Real.sqrt (d : ℝ) / 3)) / Real.sqrt (d : ℝ) := by
      field_simp [ne_of_gt hsqrtD]
    rw [heq]
    simpa [div_eq_mul_inv, mul_assoc] using hdiv
  · have hcross :
        Real.pi * Real.sqrt (scale : ℝ) *
            Real.sinh (Real.pi * Real.sqrt (d : ℝ) / 3) ≤
          ((Rat.divInt hiNum den : ℚ) : ℝ) *
            Real.cosh (Real.pi * Real.sqrt (d : ℝ) / 2) * Real.sqrt (d : ℝ) := by
      simpa [MathConst.toReal, Rat.divInt_eq_div, mul_assoc, div_eq_mul_inv] using hhi0
    apply (div_le_iff₀ hcosh).2
    rw [hsqrt_div]
    have hdiv :
        (Real.pi * Real.sqrt (scale : ℝ) *
            Real.sinh (Real.pi * Real.sqrt (d : ℝ) / 3)) / Real.sqrt (d : ℝ) ≤
          ((Rat.divInt hiNum den : ℚ) : ℝ) *
            Real.cosh (Real.pi * Real.sqrt (d : ℝ) / 2) :=
      (div_le_iff₀ hsqrtD).2 hcross
    have heq :
        Real.pi * (Real.sqrt (scale : ℝ) / Real.sqrt (d : ℝ)) *
            Real.sinh (Real.pi * Real.sqrt (d : ℝ) / 3) =
          (Real.pi * Real.sqrt (scale : ℝ) *
            Real.sinh (Real.pi * Real.sqrt (d : ℝ) / 3)) / Real.sqrt (d : ℝ) := by
      field_simp [ne_of_gt hsqrtD]
    rw [heq]
    simpa [div_eq_mul_inv, mul_assoc] using hdiv

/-- LeanCert-backed numerical enclosure for the all-exponent closed form. -/
theorem allExponentClosedForm_cert :
    ((36 : ℚ) / 100 : ℝ) ≤ allExponentClosedForm ∧
      allExponentClosedForm ≤ ((37 : ℚ) / 100 : ℝ) := by
  simpa [allExponentClosedForm, Rat.divInt_eq_div] using
    closedForm_bounds_of_cross (scale := 48) (d := 23) (loNum := 36) (hiNum := 37)
      (den := 100) (by norm_num) (by norm_num)
      glasserRHSIntegerShift0_lower_cross_cert glasserRHSIntegerShift0_upper_cross_cert

/-- LeanCert-backed numerical enclosure for the even-exponent closed form. -/
theorem evenExponentClosedForm_cert :
    ((57733 : ℚ) / 100000 : ℝ) ≤ evenExponentClosedForm ∧
      evenExponentClosedForm ≤ ((57734 : ℚ) / 100000 : ℝ) := by
  simpa [evenExponentClosedForm, Rat.divInt_eq_div] using
    closedForm_bounds_of_cross (scale := 12) (d := 11) (loNum := 57733) (hiNum := 57734)
      (den := 100000) (by norm_num) (by norm_num)
      evenExponentClosedForm_lower_cross_cert evenExponentClosedForm_upper_cross_cert

/-- The all-exponent closed form is the `k = 0` Glasser RHS in this normalization. -/
theorem glasserRHSIntegerShift_zero_eq_allExponentClosedForm :
    glasserRHSIntegerShift 0 = allExponentClosedForm := by
  unfold glasserRHSIntegerShift allExponentClosedForm
  norm_num
  ring_nf

/-- A certified explanation of the near miss: the even closed form is not `1 / sqrt 3`. -/
theorem evenExponentClosedForm_ne_invSqrtThree :
    evenExponentClosedForm ≠ 1 / Real.sqrt 3 := by
  have heven_lt : evenExponentClosedForm < ((57735 : ℚ) / 100000 : ℝ) := by
    have h := evenExponentClosedForm_cert.2
    norm_num at h ⊢
    linarith
  have hinv_ge : ((57735 : ℚ) / 100000 : ℝ) ≤ 1 / Real.sqrt 3 := by
    rw [le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
    have hsquare :
        (((57735 : ℚ) / 100000 : ℝ) * Real.sqrt 3) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    exact (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ ((57735 : ℚ) / 100000 : ℝ) * Real.sqrt 3)
      (by norm_num : (0 : ℝ) ≤ 1)).1 hsquare
  exact ne_of_lt (lt_of_lt_of_le heven_lt hinv_ge)

end ProductInvariants
