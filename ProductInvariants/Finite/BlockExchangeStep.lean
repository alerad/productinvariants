import ProductInvariants.Finite.BlockExchangePow

/-!
# The block-exchange step in genuine `uᵖ` form

This file packages the deep block-exchange descent into the **single-step descent
interface** used by the antichain-minimization layer.

## The combinatorial picture

A prime-exchange step takes a finite exponent support

  `A = B ∪ {t₁p, …, tₖp}`

(`B` the *context*, `p` a prime, and `t₁,…,tₖ ≥ 2` the multipliers, so the
`tᵢp` are the multiples of `p` in `A`) and replaces the whole block of multiples
by the single prime `p`:

  `A' = B ∪ {p}`.

The induced change in the phase integral is, **exactly** (and now *proved*, not
assumed),

  `F(A) − F(A') = ∫₀¹ P[B](u) · blockE T(uᵖ) du`,        (★)

where `T = {t₁,…,tₖ}` is the **quotient antichain** (all members `≥ 2`).

## The genuine descent quantity

Earlier drafts carried the difference in a *post-substitution* `v`-variable
`descentDiff B T = ∫₀¹ P[B](v)·blockE T(v) dv`, with `(★)` left as an unproved
interface field `subst_id`.  That identity is **false** — the change of variables
`v = uᵖ` has a non-vanishing Jacobian, so the genuine difference keeps the block
argument at `uᵖ`.  (Counterexample: `B = ∅`, `p = 2`, `T = {2}`:
`F({4}) − F({2}) = 2/15`, but `∫₀¹(v − v²)dv = 1/6`.)

The correct quantity is therefore

  `descentDiffPow B p T := ∫₀¹ P[B](u) · blockE T(uᵖ) du`,

and `(★)` is now a genuine **theorem** (`phaseIntegral_blockStep_diff` from
`BlockExchangePow.lean`), built from the pointwise product algebra
`P[A](u) − P[A'](u) = P[B](u)·blockE T(uᵖ)`.  Its sign is supplied by the powered
weighted descent:

* `descentDiffPow_nonneg` :  `0 ≤ descentDiffPow B p T`        (`F` does not increase);
* `descentDiffPow_pos`    :  `0 < descentDiffPow B p T`  when `B ≠ ∅`  (strict).

No `rpow` bookkeeping is left as an interface: the substitution identity is
discharged here.
-/

open MeasureTheory intervalIntegral Set

namespace ProductInvariants

/-- The **genuine descent difference** of a block-exchange step with context `B`,
prime base `p`, and quotient antichain `T`:

  `descentDiffPow B p T = ∫₀¹ P[B](u) · blockE T(uᵖ) du`.

This equals `F(A) − F(A')` *exactly* for `A = B ∪ {t·p : t ∈ T}`, `A' = insert p B`
(see `phaseIntegral_blockStep_diff`). -/
noncomputable def descentDiffPow (B : Finset ℕ) (p : ℕ) (T : Finset ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, phaseProduct B u * blockE T (u ^ p)

/-- **The exchange step never increases `F`**: `0 ≤ descentDiffPow B p T` whenever
`p ≥ 1` and the quotient antichain `T` consists of integers `≥ 2`.  Immediate from
`weighted_blockE_pow_nonneg`. -/
theorem descentDiffPow_nonneg (B : Finset ℕ) {p : ℕ} (hp : 1 ≤ p)
    {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) :
    0 ≤ descentDiffPow B p T := by
  unfold descentDiffPow
  exact weighted_blockE_pow_nonneg B hp hT

/-- **The exchange step strictly decreases `F`** when the context is nonempty:
`0 < descentDiffPow B p T` for nonempty `B` of positive integers, `p ≥ 1`, and
quotient antichain `T ⊆ {≥2}`.  Immediate from
`weighted_blockE_pow_pos_of_nonempty`. -/
theorem descentDiffPow_pos {B : Finset ℕ} (hB : B.Nonempty) (hB1 : ∀ n ∈ B, 1 ≤ n)
    {p : ℕ} (hp : 1 ≤ p) {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) :
    0 < descentDiffPow B p T := by
  unfold descentDiffPow
  exact weighted_blockE_pow_pos_of_nonempty hB hB1 hp hT

/-! ## The substitution step, with `(★)` now proved

`IsSubstStepFor` records the combinatorial data of a single prime-`p`
block-exchange step.  Unlike the earlier draft, the substitution identity `(★)`
is **not** a field: it is derived from the carried disjointness / injectivity /
membership data via `phaseIntegral_blockStep_diff`. -/

/-- `IsSubstStepFor B p T A A'` asserts that `A` and `A'` are the two sides of a
single prime-`p` block-exchange step with context `B` and quotient antichain `T`:

  `A = B ∪ {t*p : t ∈ T}`,  `A' = insert p B`,

together with the structural hypotheses making the block a genuine *disjoint
injective image* (so the product algebra of `(★)` applies):

* `disj`  : `B` is disjoint from the scaled block `T·p`;
* `notMem`: the prime base `p` is not already in the context `B`;
* `inj`   : scaling `· * p` is injective on `T`.

The substitution identity `F(A) − F(A') = descentDiffPow B p T` is then a
*theorem* (`IsSubstStepFor.subst_id`), not an assumption. -/
structure IsSubstStepFor (B : Finset ℕ) (p : ℕ) (T : Finset ℕ)
    (A A' : Finset ℕ) : Prop where
  block_eq : A = B ∪ T.image (· * p)
  prime_eq : A' = insert p B
  disj : Disjoint B (T.image (· * p))
  notMem : p ∉ B
  inj : Set.InjOn (· * p) T

/-- **The substitution identity `(★)`, now proved.** For any valid block-exchange
step, the genuine phase-integral difference equals the powered descent quantity:

  `F(A) − F(A') = descentDiffPow B p T`. -/
theorem IsSubstStepFor.subst_id {B : Finset ℕ} {p : ℕ} {T A A' : Finset ℕ}
    (h : IsSubstStepFor B p T A A') :
    phaseIntegral A - phaseIntegral A' = descentDiffPow B p T := by
  rw [h.block_eq, h.prime_eq]
  exact phaseIntegral_blockStep_diff h.disj h.notMem h.inj

/-- **Single block-exchange descent step.** Given a valid step and a quotient
antichain `T ⊆ {≥2}` with `p ≥ 1`, the prime side has no larger phase integral:
`F(A') ≤ F(A)`. -/
theorem phaseIntegral_substStep_le {B : Finset ℕ} {p : ℕ} {T A A' : Finset ℕ}
    (h : IsSubstStepFor B p T A A') (hp : 1 ≤ p) (hT : ∀ n ∈ T, 2 ≤ n) :
    phaseIntegral A' ≤ phaseIntegral A := by
  have hge : 0 ≤ phaseIntegral A - phaseIntegral A' := by
    rw [h.subst_id]; exact descentDiffPow_nonneg B hp hT
  linarith

/-- **Strict single block-exchange descent step** (nonempty context):
`F(A') < F(A)`. -/
theorem phaseIntegral_substStep_lt {B : Finset ℕ} {p : ℕ} {T A A' : Finset ℕ}
    (h : IsSubstStepFor B p T A A') (hB : B.Nonempty) (hB1 : ∀ n ∈ B, 1 ≤ n)
    (hp : 1 ≤ p) (hT : ∀ n ∈ T, 2 ≤ n) :
    phaseIntegral A' < phaseIntegral A := by
  have hgt : 0 < phaseIntegral A - phaseIntegral A' := by
    rw [h.subst_id]; exact descentDiffPow_pos hB hB1 hp hT
  linarith

/-! ## Iterated descent

A *descent step* is the existence of a valid block-exchange taking `A` to `A'`
with a quotient antichain of integers `≥ 2` and a prime base `p ≥ 1`.  Its
reflexive–transitive closure is a multi-step descent, along which `F` is monotone
(non-increasing).  This is the mechanism that drives an arbitrary maximal
antichain down towards the prime antichain. -/

/-- One admissible block-exchange descent step `A ⟶ A'`: there exist a context
`B`, a prime base `p ≥ 1`, and a quotient antichain `T ⊆ {≥2}` realising
`IsSubstStepFor B p T A A'`. -/
def DescentStep (A A' : Finset ℕ) : Prop :=
  ∃ (B : Finset ℕ) (p : ℕ) (T : Finset ℕ),
    1 ≤ p ∧ (∀ n ∈ T, 2 ≤ n) ∧ IsSubstStepFor B p T A A'

/-- A single descent step does not increase `F`. -/
theorem phaseIntegral_descentStep_le {A A' : Finset ℕ} (h : DescentStep A A') :
    phaseIntegral A' ≤ phaseIntegral A := by
  obtain ⟨B, p, T, hp, hT, hstep⟩ := h
  exact phaseIntegral_substStep_le hstep hp hT

/-- The reflexive–transitive closure of `DescentStep`: a finite descent *path*
`A ⟶* A'`. -/
def DescentPath : Finset ℕ → Finset ℕ → Prop :=
  Relation.ReflTransGen DescentStep

/-- **Iterated descent is monotone.** Along any finite descent path
`A ⟶* A'`, the phase integral does not increase: `F(A') ≤ F(A)`. -/
theorem phaseIntegral_descentPath_le {A A' : Finset ℕ} (h : DescentPath A A') :
    phaseIntegral A' ≤ phaseIntegral A := by
  induction h with
  | refl => exact le_refl _
  | tail _hpath hstep ih =>
      exact le_trans (phaseIntegral_descentStep_le hstep) ih

/-- **The descent target is a lower bound.** If every maximal antichain `A` in a
family admits a descent path to a common target `A₀`, then `A₀` realises the
minimum of `F` over the family: `F(A₀) ≤ F(A)` for all such `A`. -/
theorem phaseIntegral_target_le_of_descentPath {A₀ A : Finset ℕ}
    (h : DescentPath A A₀) :
    phaseIntegral A₀ ≤ phaseIntegral A :=
  phaseIntegral_descentPath_le h

end ProductInvariants
