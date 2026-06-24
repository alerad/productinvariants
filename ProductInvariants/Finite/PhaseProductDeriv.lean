import ProductInvariants.Finite.Integral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Derivative facts for the phase product weight `P[B]`

The deep block-exchange descent uses the weighted running-positivity engine
(`integral_weight_mul_nonneg`, `integral_weight_mul_pos`) with the **weight**
`w = P[B] = phaseProduct B`, which is a nonnegative, *decreasing* phase product.

This file supplies the concrete analytic facts about that weight required by the
abstract engine:

* `hasDerivAt_phaseProduct` — `P[B]` is differentiable, with explicit derivative
  `phaseProduct' B u = ∑_{i∈B} (∏_{j∈B.erase i}(1-uʲ)) · (-(i·u^{i-1}))`.
* `phaseProduct'_nonpos` — that derivative is `≤ 0` on `[0,1]` (so `P[B]` is
  decreasing): each summand is `(nonneg erased product) · (-(i·u^{i-1})) ≤ 0`.
* `continuous_phaseProduct'` — the derivative is continuous.
* `phaseProduct_one` — `P[B](1) = 0` whenever `B` is nonempty (so the boundary
  weight `w 1 ≥ 0` holds, in fact with equality), and `P[∅](1) = 1`.

These are exactly the `hw`, `hw'nonpos`, `hw'cont`, `hwnonneg` hypotheses of the
abstract weighted lemmas.
-/

open MeasureTheory intervalIntegral Set

namespace ProductInvariants

/-- The (explicit) derivative of the phase product `P[B]`:
`phaseProduct' B u = ∑_{i∈B} (∏_{j∈B.erase i}(1-uʲ)) · (-(i·u^{i-1}))`. -/
noncomputable def phaseProduct' (B : Finset ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ B, (∏ j ∈ B.erase i, (1 - u ^ j)) * (-((i : ℝ) * u ^ (i - 1)))

/-- `1 - u^n` has derivative `-(n·u^{n-1})`. -/
theorem hasDerivAt_one_sub_pow (n : ℕ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => 1 - u ^ n) (-((n : ℝ) * u ^ (n - 1))) u := by
  have h := (hasDerivAt_pow n u)
  simpa using (hasDerivAt_const u (1 : ℝ)).sub h

/-- **The phase product weight is differentiable** with derivative `phaseProduct'`. -/
theorem hasDerivAt_phaseProduct (B : Finset ℕ) (u : ℝ) :
    HasDerivAt (phaseProduct B) (phaseProduct' B u) u := by
  classical
  have h :
      HasDerivAt (fun u : ℝ => ∏ i ∈ B, (1 - u ^ i))
        (∑ i ∈ B, (∏ j ∈ B.erase i, (1 - u ^ j)) • (-((i : ℝ) * u ^ (i - 1)))) u :=
    HasDerivAt.fun_finset_prod (fun i _hi => hasDerivAt_one_sub_pow i u)
  simpa [phaseProduct, phaseProduct', smul_eq_mul] using h

/-- **The phase product weight is decreasing**: its derivative is `≤ 0` on `[0,1]`. -/
theorem phaseProduct'_nonpos (B : Finset ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    phaseProduct' B u ≤ 0 := by
  classical
  unfold phaseProduct'
  apply Finset.sum_nonpos
  intro i _hi
  -- `(∏ erased (1-uʲ)) ≥ 0` and `i·u^{i-1} ≥ 0`, so the product with `-(…)` is `≤ 0`.
  have hprod : 0 ≤ ∏ j ∈ B.erase i, (1 - u ^ j) :=
    Finset.prod_nonneg (fun j _hj => one_sub_pow_nonneg_of_mem_Icc hu j)
  have hpow : 0 ≤ (i : ℝ) * u ^ (i - 1) :=
    mul_nonneg (by positivity) (pow_nonneg hu.1 _)
  have : 0 ≤ (∏ j ∈ B.erase i, (1 - u ^ j)) * ((i : ℝ) * u ^ (i - 1)) :=
    mul_nonneg hprod hpow
  linarith [this]

/-- The derivative `phaseProduct'` is continuous. -/
theorem continuous_phaseProduct' (B : Finset ℕ) :
    Continuous (phaseProduct' B) := by
  classical
  unfold phaseProduct'
  apply continuous_finset_sum
  intro i _hi
  apply Continuous.mul
  · exact continuous_finset_prod _ (fun j _hj => continuous_const.sub (continuous_pow j))
  · exact (continuous_const.mul (continuous_pow _)).neg

/-- `P[∅](1) = 1`. -/
@[simp] theorem phaseProduct_one_empty : phaseProduct (∅ : Finset ℕ) 1 = 1 := by
  simp

/-- For a nonempty support, the weight vanishes at the right endpoint: `P[B](1) = 0`. -/
theorem phaseProduct_one_of_nonempty {B : Finset ℕ} (hB : B.Nonempty) :
    phaseProduct B 1 = 0 := by
  classical
  obtain ⟨i, hi⟩ := hB
  unfold phaseProduct
  apply Finset.prod_eq_zero hi
  simp

/-- In all cases the right-endpoint weight is nonnegative (`= 0` if `B ≠ ∅`,
`= 1` if `B = ∅`). -/
theorem phaseProduct_one_nonneg (B : Finset ℕ) : 0 ≤ phaseProduct B 1 := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · simp [hB]
  · simp [phaseProduct_one_of_nonempty hB]

end ProductInvariants
