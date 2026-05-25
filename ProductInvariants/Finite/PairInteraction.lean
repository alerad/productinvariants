import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-!
# Pair interaction for product-integral invariants

This file records the closed-form two-exponent interaction that appears after
expanding

`∫_0^1 (1 - u^p) (1 - u^q) du`.

The theorem is stated algebraically over positive real exponents. For positive
integer exponents, the quantities are exactly the singleton and pair
product-integrals.
-/

namespace ProductInvariants

/-!
For one exponent `p`, the product-integral is

`F_p = ∫_0^1 (1 - u^p) du = p / (p + 1)`.

For two exponents `p,q`, the expanded integral is

`F_pq = 1 - 1/(p+1) - 1/(q+1) + 1/(p+q+1)`.

The ratio `F_pq / (F_p * F_q)` measures the failure of the pair integral to
factor as independent singleton contributions. It has the exact closed form
below.
-/

/-- Exact closed form for the two-exponent product-integral interaction. -/
theorem exact_pair_interaction (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    let Fp := p / (p + 1)
    let Fq := q / (q + 1)
    let Fpq := 1 - 1 / (p + 1) - 1 / (q + 1) + 1 / (p + q + 1)
    Fpq / (Fp * Fq) = 1 + 1 / (p + q + 1) := by
  have hp1 : p + 1 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by positivity
  have hpq1 : p + q + 1 ≠ 0 := by positivity
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have hq_ne : q ≠ 0 := ne_of_gt hq
  dsimp only
  field_simp
  ring

/-- Log-space form of the pair interaction. -/
noncomputable def pairInteractionEnergy (p q : ℝ) : ℝ :=
  -Real.log (1 + 1 / (p + q + 1))

/-- The pair interaction energy is non-positive for positive exponents. -/
theorem pairInteractionEnergy_nonpos (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    pairInteractionEnergy p q ≤ 0 := by
  unfold pairInteractionEnergy
  simp only [neg_nonpos]
  apply Real.log_nonneg
  have : 0 < 1 / (p + q + 1) := by positivity
  linarith

end ProductInvariants
