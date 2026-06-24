import ProductInvariants.Finite.BlockEPartial
import ProductInvariants.Finite.PhaseProductDeriv
import ProductInvariants.Finite.WeightedRunningPositivity

/-!
# The deep block-exchange descent (weighted form)

This file assembles the **deep block-exchange descent inequality** — the
"crux finish line" — from the three pieces built in the preceding files:

* the universal partial positivity of the block integrand
  (`blockE_partial_pos`, from the tail-domination certificate);
* the analytic weight facts for the phase product `P[B]`
  (`hasDerivAt_phaseProduct`, `phaseProduct'_nonpos`, `continuous_phaseProduct'`,
  `phaseProduct_one_nonneg`, from `PhaseProductDeriv`);
* the abstract integration-by-parts engine
  (`integral_weight_mul_nonneg`, `integral_weight_mul_pos`, from
  `WeightedRunningPositivity`).

## The statement

For an arbitrary finite "context" support `B` and a finite "block" support
`T ⊆ {2,3,…}`, the weighted block integral is nonnegative:

  `0 ≤ ∫₀¹ P[B](v) · blockE T(v) dv`,

and it is **strictly** positive when `B` is nonempty (more precisely, when the
weight `P[B]` is genuinely decreasing somewhere on `(0,1)`).

This is the analytic heart of the prime block-exchange step
`F(A') ≤ F(A)`: with `A = B ∪ {t₁p,…,tₖp}` and `A' = B ∪ {p}`, the difference
`F(A) − F(A')` equals `∫₀¹ P[B](v) · blockE T(v) dv` after the substitution
`v = uᵖ` (carried out in the antichain-assembly layer).  Here `T = {t₁,…,tₖ}`
is the **quotient antichain**, whose members are all `≥ 2`, which is exactly the
hypothesis under which `blockE_partial_pos` applies.
-/

open MeasureTheory intervalIntegral Set

namespace ProductInvariants

/-- **The deep block-exchange descent inequality (nonnegative form).**

For any finite context support `B` and any finite block support `T` of integers
`≥ 2`, the weighted block integral is nonnegative:

  `0 ≤ ∫₀¹ P[B](v) · blockE T(v) dv`.

The weight `w = P[B]` is nonnegative and decreasing (`w' ≤ 0`,
`phaseProduct'_nonpos`) with `w(1) ≥ 0` (`phaseProduct_one_nonneg`); the
integrand factor `g = blockE T` has nonnegative running integrals on `[0,1]`
(`blockE_partial_pos`).  Integration by parts (`integral_weight_mul_nonneg`)
delivers the conclusion. -/
theorem weighted_blockE_nonneg (B : Finset ℕ) {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) :
    0 ≤ ∫ v in (0 : ℝ)..1, phaseProduct B v * blockE T v := by
  refine integral_weight_mul_nonneg
    (g := blockE T) (w := phaseProduct B) (w' := phaseProduct' B)
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- `g = blockE T` is continuous.
    unfold blockE phaseProduct
    fun_prop
  · -- `w = P[B]` is differentiable with derivative `phaseProduct' B`.
    intro x _hx
    exact hasDerivAt_phaseProduct B x
  · -- `w'` is interval-integrable.
    exact (continuous_phaseProduct' B).intervalIntegrable 0 1
  · -- `w 1 ≥ 0`.
    exact phaseProduct_one_nonneg B
  · -- `w' ≤ 0` on `[0,1]`.
    intro x hx
    exact phaseProduct'_nonpos B hx
  · -- the running integrals `∫₀ᶜ blockE T ≥ 0` on `[0,1]`.
    intro c hc
    rcases eq_or_lt_of_le hc.1 with h | h
    · simp [← h]
    · exact (blockE_partial_pos hT ⟨h, hc.2⟩).le

/-- **The deep block-exchange descent inequality (strict form).**

If, in addition to the hypotheses of `weighted_blockE_nonneg`, the weight
`P[B]` is *genuinely decreasing* at some interior point — i.e. there is
`x₀ ∈ (0,1)` with `phaseProduct' B x₀ < 0` — then the weighted block integral is
**strictly** positive:

  `0 < ∫₀¹ P[B](v) · blockE T(v) dv`.

(A sufficient concrete condition for the witness is that `B` is nonempty; see
`weighted_blockE_pos_of_nonempty`.) -/
theorem weighted_blockE_pos (B : Finset ℕ) {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hx₀' : phaseProduct' B x₀ < 0) :
    0 < ∫ v in (0 : ℝ)..1, phaseProduct B v * blockE T v := by
  refine integral_weight_mul_pos
    (g := blockE T) (w := phaseProduct B) (w' := phaseProduct' B)
    ?_ ?_ ?_ ?_ ?_ ?_ hx₀ hx₀'
  · unfold blockE phaseProduct; fun_prop
  · intro x _hx; exact hasDerivAt_phaseProduct B x
  · exact continuous_phaseProduct' B
  · exact phaseProduct_one_nonneg B
  · intro x hx; exact phaseProduct'_nonpos B hx
  · intro c hc; exact blockE_partial_pos hT hc

/-- For a support `B` of positive integers that is nonempty, the weight `P[B]`
is **strictly** decreasing at every interior point: `phaseProduct' B x < 0` for
`x ∈ (0,1)`.

Picking any `i ∈ B`, the `i`-th summand
`(∏_{j∈B.erase i}(1-xʲ)) · (-(i·x^{i-1}))` is strictly negative on `(0,1)` — the
erased product is a product of strictly positive factors `1-xʲ > 0` (using
`j ≥ 1`), and `i·x^{i-1} > 0` — while every other summand is `≤ 0`. -/
theorem phaseProduct'_neg_of_nonempty {B : Finset ℕ} (hB : B.Nonempty)
    (hB1 : ∀ n ∈ B, 1 ≤ n) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    phaseProduct' B x < 0 := by
  classical
  obtain ⟨i, hi⟩ := hB
  -- strict positivity of `1 - xʲ` on `(0,1)` for `j ≥ 1`
  have hfac : ∀ j : ℕ, 1 ≤ j → 0 < 1 - x ^ j := by
    intro j hj
    have : x ^ j < 1 := by
      calc x ^ j ≤ x ^ 1 := pow_le_pow_of_le_one hx.1.le hx.2.le hj
        _ = x := pow_one x
        _ < 1 := hx.2
    linarith
  -- the erased product is strictly positive (all factors `> 0`)
  have herased : 0 < ∏ j ∈ B.erase i, (1 - x ^ j) :=
    Finset.prod_pos (fun j hj => hfac j (hB1 j (Finset.mem_of_mem_erase hj)))
  -- `i · x^{i-1} > 0`
  have hi1 : 1 ≤ i := hB1 i hi
  have hpow : 0 < (i : ℝ) * x ^ (i - 1) := by
    have : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
    exact mul_pos this (pow_pos hx.1 _)
  -- the `i`-th summand is strictly negative
  have hineg : (∏ j ∈ B.erase i, (1 - x ^ j)) * (-((i : ℝ) * x ^ (i - 1))) < 0 := by
    have := mul_pos herased hpow
    linarith
  -- every summand is `≤ 0`; the `i`-th is `< 0`, so the sum is `< 0`.
  unfold phaseProduct'
  have hsum_le : ∀ j ∈ B,
      (∏ k ∈ B.erase j, (1 - x ^ k)) * (-((j : ℝ) * x ^ (j - 1))) ≤ 0 := by
    intro j _hj
    have hprod : 0 ≤ ∏ k ∈ B.erase j, (1 - x ^ k) :=
      Finset.prod_nonneg (fun k _hk =>
        one_sub_pow_nonneg_of_mem_Icc ⟨hx.1.le, hx.2.le⟩ k)
    have hpow' : 0 ≤ (j : ℝ) * x ^ (j - 1) :=
      mul_nonneg (by positivity) (pow_nonneg hx.1.le _)
    nlinarith [mul_nonneg hprod hpow']
  have : (∑ j ∈ B, (∏ k ∈ B.erase j, (1 - x ^ k)) * (-((j : ℝ) * x ^ (j - 1))))
      < ∑ _j ∈ B, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro j hj; simpa using hsum_le j hj
    · exact ⟨i, hi, by simpa using hineg⟩
  simpa using this

/-- **The deep block-exchange descent (strict, nonempty-context form).**

If the context support `B` is nonempty (and consists of positive integers) and
the block `T` consists of integers `≥ 2`, then

  `0 < ∫₀¹ P[B](v) · blockE T(v) dv`.

This is the convenient packaging of `weighted_blockE_pos` with the interior
witness `x₀ = 1/2` supplied by `phaseProduct'_neg_of_nonempty`. -/
theorem weighted_blockE_pos_of_nonempty {B : Finset ℕ} (hB : B.Nonempty)
    (hB1 : ∀ n ∈ B, 1 ≤ n) {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) :
    0 < ∫ v in (0 : ℝ)..1, phaseProduct B v * blockE T v := by
  have hx₀ : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  exact weighted_blockE_pos B hT hx₀
    (phaseProduct'_neg_of_nonempty hB hB1 hx₀)

end ProductInvariants
