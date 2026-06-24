import ProductInvariants.Finite.BlockExchangeDescent
import ProductInvariants.Finite.PowerSubstitution

/-!
# The powered block-exchange descent (genuine `uᵖ` form)

`BlockExchangeDescent.lean` proves the weighted descent with the block argument
at `v`:

  `0 ≤ ∫₀¹ P[B](v) · blockE T(v) dv`.

The *genuine* block-exchange difference of a prime-`p` step, however, has the
block argument at `uᵖ`:

  `F(A) − F(A') = ∫₀¹ P[B](u) · blockE T(uᵖ) du`.

This file proves the corresponding nonnegativity directly in the `uᵖ` form, by
feeding the **composed** running-positivity certificate
`running_pos_comp_pow` (from `PowerSubstitution.lean`) into the same weighted
IBP engine with weight `w = P[B]`:

  `0 ≤ ∫₀¹ P[B](u) · blockE T(uᵖ) du`,

strict when the context `B` is nonempty.  This is the analytic content actually
required by the antichain-minimization layer; no `rpow` bookkeeping is left as an
interface.
-/

open MeasureTheory intervalIntegral Set

namespace ProductInvariants

/-- **The powered deep block-exchange descent (nonnegative form).**

For any finite context `B`, prime power `p ≥ 1`, and block `T ⊆ {≥2}`,

  `0 ≤ ∫₀¹ P[B](u) · blockE T(uᵖ) du`.

Same proof shape as `weighted_blockE_nonneg`, but the running-integral
hypothesis is supplied by `running_pos_comp_pow` for the composed integrand
`u ↦ blockE T(uᵖ)`. -/
theorem weighted_blockE_pow_nonneg (B : Finset ℕ) {p : ℕ} (hp : 1 ≤ p)
    {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) :
    0 ≤ ∫ u in (0 : ℝ)..1, phaseProduct B u * blockE T (u ^ p) := by
  refine integral_weight_mul_nonneg
    (g := fun u => blockE T (u ^ p)) (w := phaseProduct B) (w' := phaseProduct' B)
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- `g u = blockE T (uᵖ)` is continuous.
    exact (continuous_blockE T).comp (continuous_pow p)
  · intro x _hx; exact hasDerivAt_phaseProduct B x
  · exact (continuous_phaseProduct' B).intervalIntegrable 0 1
  · exact phaseProduct_one_nonneg B
  · intro x hx; exact phaseProduct'_nonpos B hx
  · -- running integrals `∫₀ᶜ blockE T(uᵖ) ≥ 0` on `[0,1]`.
    intro c hc
    exact running_pos_comp_pow hT hp hc

/-- **The powered deep block-exchange descent (strict, nonempty-context form).**

If the context `B` is nonempty (of positive integers) and `T ⊆ {≥2}`, then

  `0 < ∫₀¹ P[B](u) · blockE T(uᵖ) du`. -/
theorem weighted_blockE_pow_pos_of_nonempty {B : Finset ℕ} (hB : B.Nonempty)
    (hB1 : ∀ n ∈ B, 1 ≤ n) {p : ℕ} (hp : 1 ≤ p)
    {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) :
    0 < ∫ u in (0 : ℝ)..1, phaseProduct B u * blockE T (u ^ p) := by
  have hx₀ : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  refine integral_weight_mul_pos
    (g := fun u => blockE T (u ^ p)) (w := phaseProduct B) (w' := phaseProduct' B)
    ?_ ?_ ?_ ?_ ?_ ?_ hx₀ (phaseProduct'_neg_of_nonempty hB hB1 hx₀)
  · exact (continuous_blockE T).comp (continuous_pow p)
  · intro x _hx; exact hasDerivAt_phaseProduct B x
  · exact continuous_phaseProduct' B
  · exact phaseProduct_one_nonneg B
  · intro x hx; exact phaseProduct'_nonpos B hx
  · intro c hc; exact running_pos_comp_pow_pos hT hp hc

/-! ## Block-step product algebra

The genuine prime-`p` substitution step replaces the multiples `T·p` (an injective
image of a block `T`) by the single prime `p`, keeping the disjoint context `B`
fixed.  The pointwise difference of the two phase products factors exactly as the
context product times the *block integrand at `uᵖ`*. -/

/-- Scaling the exponents by `p` reindexes the phase product as evaluation at `uᵖ`:
`P[T·p](u) = P[T](uᵖ)`, provided `· * p` is injective on `T`. -/
theorem phaseProduct_image_mul (T : Finset ℕ) (p : ℕ)
    (hinj : Set.InjOn (· * p) T) (u : ℝ) :
    phaseProduct (T.image (· * p)) u = phaseProduct T (u ^ p) := by
  unfold phaseProduct
  rw [Finset.prod_image (fun a ha b hb => hinj ha hb)]
  refine Finset.prod_congr rfl (fun n _hn => ?_)
  rw [← pow_mul, mul_comm n p]

/-- The phase product splits over a disjoint union:
`P[B ∪ S](u) = P[B](u) · P[S](u)`. -/
theorem phaseProduct_union {B S : Finset ℕ} (hdisj : Disjoint B S) (u : ℝ) :
    phaseProduct (B ∪ S) u = phaseProduct B u * phaseProduct S u := by
  unfold phaseProduct
  rw [Finset.prod_union hdisj]

/-- **Pointwise block-step product identity.**

For a substitution step with disjoint context `B`, injective scaling block
`T.image (· * p)`, and prime `p ∉ B`:

  `P[B ∪ T·p](u) − P[insert p B](u) = P[B](u) · blockE T (uᵖ)`. -/
theorem phaseProduct_blockStep_diff {B T : Finset ℕ} {p : ℕ}
    (hdisj : Disjoint B (T.image (· * p))) (hpB : p ∉ B)
    (hinj : Set.InjOn (· * p) T) (u : ℝ) :
    phaseProduct (B ∪ T.image (· * p)) u - phaseProduct (insert p B) u
      = phaseProduct B u * blockE T (u ^ p) := by
  rw [phaseProduct_union hdisj, phaseProduct_image_mul T p hinj,
    phaseProduct_insert hpB]
  unfold blockE
  ring

/-- **Integrated block-step identity.**

The genuine phase-integral difference of a prime-`p` substitution step equals the
powered weighted block integral:

  `F(B ∪ T·p) − F(insert p B) = ∫₀¹ P[B](u) · blockE T (uᵖ) du`. -/
theorem phaseIntegral_blockStep_diff {B T : Finset ℕ} {p : ℕ}
    (hdisj : Disjoint B (T.image (· * p))) (hpB : p ∉ B)
    (hinj : Set.InjOn (· * p) T) :
    phaseIntegral (B ∪ T.image (· * p)) - phaseIntegral (insert p B)
      = ∫ u in (0 : ℝ)..1, phaseProduct B u * blockE T (u ^ p) := by
  unfold phaseIntegral
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_phaseProduct _) (intervalIntegrable_phaseProduct _)]
  refine intervalIntegral.integral_congr (fun u _hu => ?_)
  exact phaseProduct_blockStep_diff hdisj hpB hinj u

end ProductInvariants
