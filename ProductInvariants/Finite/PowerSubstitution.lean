import ProductInvariants.Finite.BlockEPartial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Running positivity is preserved under the power substitution `u ↦ uᵖ`

The genuine block-exchange difference of a prime-`p` step is

  `F(A) − F(A') = ∫₀¹ P[B](u) · blockE T(uᵖ) du`,

with the block argument at `uᵖ`.  To feed this into the weighted IBP engine
(`integral_weight_mul_nonneg`) we must know that the *composed* integrand
`u ↦ blockE T(uᵖ)` still has nonnegative running integrals:

  `0 ≤ ∫₀ᶜ blockE T(uᵖ) du`   for all `c ∈ [0,1]`.

The proven input is the plain running positivity `0 ≤ ∫₀ᵈ blockE T v`
(`blockE_partial_pos`).  The bridge is the change of variables `v = uᵖ`.

## Strategy

Let `G(d) = ∫₀ᵈ blockE T` (nonnegative, `G(0)=0`, `G' = blockE T`).
The map `A(u) := G(uᵖ)` has, by the chain rule,

  `A'(u) = blockE T(uᵖ) · p · u^{p-1}`,

so `A` is a genuine antiderivative of `blockE T(uᵖ) · p·u^{p-1}` with **no
fractional powers**.  Integration by parts against `B(u) = u^{1-p}/p`,

  `∫₀ᶜ blockE T(uᵖ) du = ∫₀ᶜ A'(u) B(u) du
                        = [A B]₀ᶜ − ∫₀ᶜ A B'`,

has clean signs: the upper boundary `A(c)B(c)=G(cᵖ)c^{1-p}/p ≥ 0`, the lower
boundary vanishes (`G(uᵖ)=O(uᵖ)` kills the singular `u^{1-p}`), and the tail
`−∫ A B' = (p-1)/p ∫ G(uᵖ) u^{-p} ≥ 0` since `B' ≤ 0` and `A ≥ 0`.

To stay within the regular interval-integral API we avoid the improper lower
boundary by working on `[ε, c]` and letting `ε ↓ 0`.
-/

open MeasureTheory intervalIntegral Set

namespace ProductInvariants

/-- The running integral of the block integrand, `G T d = ∫₀ᵈ blockE T`. -/
noncomputable def blockRun (T : Finset ℕ) (d : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..d, blockE T v

/-- `blockE T` is continuous. -/
theorem continuous_blockE (T : Finset ℕ) : Continuous (blockE T) := by
  unfold blockE phaseProduct
  fun_prop

/-- `blockRun T` is the antiderivative of `blockE T`: `(blockRun T)' = blockE T`. -/
theorem hasDerivAt_blockRun (T : Finset ℕ) (d : ℝ) :
    HasDerivAt (blockRun T) (blockE T d) d := by
  unfold blockRun
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_blockE T).intervalIntegrable 0 d)
    ((continuous_blockE T).stronglyMeasurableAtFilter _ _)
    (continuous_blockE T).continuousAt

/-- `blockRun T` is continuous (it is a primitive of the continuous `blockE T`). -/
theorem continuous_blockRun (T : Finset ℕ) : Continuous (blockRun T) :=
  continuous_iff_continuousAt.mpr (fun d => (hasDerivAt_blockRun T d).continuousAt)

/-- `blockRun T 0 = 0`. -/
@[simp] theorem blockRun_zero (T : Finset ℕ) : blockRun T 0 = 0 := by
  simp [blockRun]

/-- `blockRun T` is nonnegative for `T ⊆ {≥2}` on `[0,∞)` (really on `[0,1]`,
but we only use `d ∈ [0,1]`). -/
theorem blockRun_nonneg {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) 1) : 0 ≤ blockRun T d := by
  rcases eq_or_lt_of_le hd.1 with h | h
  · simp [blockRun, ← h]
  · exact (blockE_partial_pos hT ⟨h, hd.2⟩).le

/-! ## The polynomial change of variables `v = uᵖ`

For `p ≥ 1` the map `u ↦ uᵖ` is a polynomial substitution (no fractional
powers), so the forward change of variables
`∫₀ᶜ (blockE T)(uᵖ) · p·u^{p-1} du = ∫₀^{cᵖ} blockE T v dv` is the regular
interval-integral CoV `integral_comp_mul_deriv_of_deriv_nonneg`. -/

/-- **Polynomial change of variables** `v = uᵖ` for the block integrand
(`p ≥ 1`, `0 ≤ c`):

  `∫₀ᶜ blockE T (uᵖ) · (p · u^{p-1}) du = ∫₀^{cᵖ} blockE T v dv = blockRun T (cᵖ)`.

The substitution map `f u = uᵖ` is a genuine polynomial, so this is the regular
(non-improper) change of variables; no `rpow` appears. -/
theorem integral_blockE_comp_pow_mul (T : Finset ℕ) {p : ℕ} (hp : 1 ≤ p)
    {c : ℝ} (hc : 0 ≤ c) :
    (∫ u in (0 : ℝ)..c, blockE T (u ^ p) * ((p : ℝ) * u ^ (p - 1))) =
      blockRun T (c ^ p) := by
  have hcov :
      (∫ u in (0 : ℝ)..c, (blockE T ∘ fun u : ℝ => u ^ p) u * ((p : ℝ) * u ^ (p - 1)))
        = ∫ v in ((fun u : ℝ => u ^ p) 0)..((fun u : ℝ => u ^ p) c), blockE T v := by
    refine integral_comp_mul_deriv_of_deriv_nonneg
      (f := fun u : ℝ => u ^ p) (f' := fun u : ℝ => (p : ℝ) * u ^ (p - 1))
      (g := blockE T) ?_ ?_ ?_
    · -- continuity of `u ↦ uᵖ`
      fun_prop
    · -- derivative of `u ↦ uᵖ`
      intro x _hx
      simpa using (hasDerivAt_pow p x)
    · -- nonnegativity of the derivative on the interior of `[0,c]`
      intro x hx
      have hx0 : 0 ≤ x := le_of_lt (by
        rw [min_eq_left hc] at hx; exact hx.1)
      positivity
  -- simplify the endpoints and the composition
  simp only [Function.comp_def] at hcov
  rw [hcov, zero_pow (Nat.one_le_iff_ne_zero.mp hp)]
  rfl

/-- A linear bound for the running integral near `0`: since `blockE T` is
continuous (hence bounded by some `M` on `[0,1]`), `|blockRun T d| ≤ M·d` for
`d ∈ [0,1]`.  This is the growth control that kills the singular lower boundary
in the change of variables. -/
theorem abs_blockRun_le (T : Finset ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ d ∈ Icc (0 : ℝ) 1, |blockRun T d| ≤ M * d := by
  -- `blockE T` is bounded on the compact `[0,1]`.
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_blockE T).continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro d hd
  have hbound : ∀ v ∈ Icc (0:ℝ) 1, |blockE T v| ≤ max M 0 := by
    intro v hv; exact (hM v hv).trans (le_max_left _ _)
  -- |∫₀ᵈ blockE| ≤ (max M 0) · |d - 0|
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := d) (C := max M 0) (f := blockE T)
    (by
      intro v hv
      have hv' : v ∈ Icc (0:ℝ) 1 := by
        rw [uIoc_of_le hd.1] at hv
        exact ⟨hv.1.le, hv.2.trans hd.2⟩
      simpa [Real.norm_eq_abs] using hbound v hv')
  simpa [blockRun, Real.norm_eq_abs, abs_of_nonneg hd.1] using this

/-! ## Running positivity under the power substitution

The central lemma: the composed integrand `u ↦ blockE T(uᵖ)` inherits
nonnegative running integrals from `blockE T`.

The proof integrates by parts on `[ε, c]` against the smooth weight
`φ(u) = u^{1-p}/p` (smooth away from `0`), with antiderivative
`A(u) = blockRun T(uᵖ)` of `blockE T(uᵖ)·p·u^{p-1}` (no fractional powers).
Both `ε`-boundary contributions vanish as `ε ↓ 0` thanks to the growth bound
`abs_blockRun_le`, and the surviving terms are manifestly nonnegative. -/

/-- The smooth weight `φ(u) = u^{1-p}/p` used to undo the Jacobian, written with
`rpow` so that its derivative is available away from `0`. -/
private noncomputable def jacWeight (p : ℕ) (u : ℝ) : ℝ :=
  u ^ ((1 : ℝ) - p) / p

/-- The derivative of `jacWeight p` away from `0`:
`φ'(u) = (1-p)/p · u^{-p}`. -/
private noncomputable def jacWeight' (p : ℕ) (u : ℝ) : ℝ :=
  ((1 : ℝ) - p) / p * u ^ ((-p : ℝ))

/-- The antiderivative `A(u) = blockRun T(uᵖ)` of `blockE T(uᵖ)·p·u^{p-1}`. -/
private noncomputable def jacAnti (T : Finset ℕ) (p : ℕ) (u : ℝ) : ℝ :=
  blockRun T (u ^ p)

/-- The tail integrand `−φ'(u)·A(u) = (p-1)/p · u^{-p}·blockRun T(uᵖ)`.
By the growth bound `|blockRun T(uᵖ)| ≤ M·uᵖ`, this is *bounded* near `0`, hence
extends to an integrable function on `[0,c]`; pointwise it is nonnegative. -/
private noncomputable def jacTail (T : Finset ℕ) (p : ℕ) (u : ℝ) : ℝ :=
  jacWeight' p u * jacAnti T p u

/-- Derivative of `jacWeight` at `u ≠ 0`. -/
private theorem hasDerivAt_jacWeight {p : ℕ} (hp : 1 ≤ p) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (jacWeight p) (jacWeight' p u) u := by
  unfold jacWeight jacWeight'
  have hbase : HasDerivAt (fun x : ℝ => x ^ ((1 : ℝ) - p))
      (((1 : ℝ) - p) * u ^ ((1 : ℝ) - p - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu)
  have hpne : (p : ℝ) ≠ 0 := by positivity
  have h := hbase.div_const (p : ℝ)
  -- rewrite the exponent `(1-p)-1 = -p`
  have hexp : (1 : ℝ) - p - 1 = (-p : ℝ) := by ring
  rw [hexp] at h
  -- `((1-p)*u^{-p})/p = (1-p)/p * u^{-p}`
  have : ((1 : ℝ) - p) * u ^ ((-p : ℝ)) / p
      = ((1 : ℝ) - p) / p * u ^ ((-p : ℝ)) := by ring
  rwa [this] at h

/-- Derivative of `jacAnti T p` at any `u` (chain rule for `blockRun ∘ (·^p)`). -/
private theorem hasDerivAt_jacAnti (T : Finset ℕ) {p : ℕ} (u : ℝ) :
    HasDerivAt (jacAnti T p) (blockE T (u ^ p) * ((p : ℝ) * u ^ (p - 1))) u := by
  unfold jacAnti
  have hout : HasDerivAt (blockRun T) (blockE T (u ^ p)) (u ^ p) :=
    hasDerivAt_blockRun T (u ^ p)
  have hin : HasDerivAt (fun x : ℝ => x ^ p) ((p : ℝ) * u ^ (p - 1)) u := by
    simpa using hasDerivAt_pow p u
  exact hout.comp u hin

/-- The key pointwise identity for `u > 0`: `φ(u)·A'(u) = blockE T(uᵖ)`.  The
Jacobian `p·u^{p-1}` exactly cancels the singular weight `u^{1-p}/p`. -/
private theorem jacWeight_mul_jacAnti_deriv {p : ℕ} (hp : 1 ≤ p) (T : Finset ℕ)
    {u : ℝ} (hu : 0 < u) :
    jacWeight p u * (blockE T (u ^ p) * ((p : ℝ) * u ^ (p - 1)))
      = blockE T (u ^ p) := by
  unfold jacWeight
  have hpne : (p : ℝ) ≠ 0 := by positivity
  -- convert the nat power `u^{p-1}` to an `rpow` so exponents combine.
  have hcast : (u : ℝ) ^ (p - 1) = u ^ ((p : ℝ) - 1) := by
    rw [← Real.rpow_natCast u (p - 1)]
    congr 1
    have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      have : 1 ≤ p := hp
      push_cast [Nat.cast_sub this]
      ring
    exact this
  rw [hcast]
  have hcomb : u ^ ((1 : ℝ) - p) * u ^ ((p : ℝ) - 1) = 1 := by
    rw [← Real.rpow_add hu]
    norm_num
  -- regroup: (u^{1-p}/p) * (b * (p * u^{p-1})) = b * (u^{1-p} * u^{p-1}) = b·1.
  have hregroup :
      u ^ ((1 : ℝ) - p) / p * (blockE T (u ^ p) * ((p : ℝ) * u ^ ((p : ℝ) - 1)))
        = blockE T (u ^ p) * (u ^ ((1 : ℝ) - p) * u ^ ((p : ℝ) - 1)) := by
    field_simp
  rw [hregroup, hcomb, mul_one]

/-- **Boundary lower bound for the composed running integral (`p ≥ 2`).**

Integrating by parts on `[ε,c]` against the smooth weight `φ(u)=u^{1-p}/p`
(smooth away from `0`) with antiderivative `A(u)=blockRun T(uᵖ)`, and passing
`ε ↓ 0` (the singular `ε`-contributions vanish by the growth bound
`abs_blockRun_le`), yields the explicit boundary lower bound

  `φ(c)·A(c) = (c^{1-p}/p)·blockRun T(cᵖ) ≤ ∫₀ᶜ blockE T(uᵖ) du`.

Both `running_pos_comp_pow_ge_two` (nonnegativity) and the strict version follow
from this, since the boundary term `φ(c)·A(c)` is `≥ 0` (and `> 0` when
`c ∈ (0,1]`). -/
theorem bdry_le_running_comp_pow {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {p : ℕ}
    (hp2 : 2 ≤ p) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hc0 : 0 < c) :
    jacWeight p c * blockRun T (c ^ p) ≤ ∫ u in (0 : ℝ)..c, blockE T (u ^ p) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp2
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  -- Abbreviations.
  set g : ℝ → ℝ := fun u => blockE T (u ^ p) with hgdef
  have hgcont : Continuous g := (continuous_blockE T).comp (continuous_pow p)
  -- `A(u) = blockRun T(uᵖ)`, the antiderivative of `g·(p·u^{p-1})`.
  -- ε-IBP identity on `[ε,c]` and the lower-bound `I(ε) ≥ φ(c)A(c) − φ(ε)A(ε)`.
  -- For `0 < ε < c`:
  have hstep : ∀ ε : ℝ, 0 < ε → ε < c →
      jacWeight p c * blockRun T (c ^ p) - jacWeight p ε * blockRun T (ε ^ p)
        ≤ ∫ u in ε..c, g u := by
    intro ε hε hεc
    -- IBP: ∫_ε^c φ·A' = [φ A]_ε^c − ∫_ε^c φ'·A.
    have hεc' : ε ≤ c := hεc.le
    have hmem : ∀ x ∈ Set.uIcc ε c, x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hεc'] at hx
      exact ne_of_gt (lt_of_lt_of_le hε hx.1)
    -- derivatives on the interval interior
    have hφderiv : ∀ x ∈ Set.uIcc ε c, HasDerivAt (jacWeight p) (jacWeight' p x) x := by
      intro x hx; exact hasDerivAt_jacWeight hp1 (hmem x hx)
    have hAderiv : ∀ x ∈ Set.uIcc ε c,
        HasDerivAt (jacAnti T p) (blockE T (x ^ p) * ((p : ℝ) * x ^ (p - 1))) x := by
      intro x _hx; exact hasDerivAt_jacAnti T x
    -- `jacWeight'` continuous on `[ε,c]` (since `ε>0`), hence interval-integrable.
    have hφ'int : IntervalIntegrable (jacWeight' p) volume ε c := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      left
      rw [Set.uIcc_of_le hεc'] at hx
      exact ne_of_gt (lt_of_lt_of_le hε hx.1)
    -- `A' = g·(p··^{p-1})` continuous, interval-integrable.
    have hA'int : IntervalIntegrable
        (fun x => blockE T (x ^ p) * ((p : ℝ) * x ^ (p - 1))) volume ε c := by
      apply Continuous.intervalIntegrable
      exact hgcont.mul (continuous_const.mul (continuous_pow _))
    have hIBP :
        (∫ x in ε..c, jacWeight p x * (blockE T (x ^ p) * ((p : ℝ) * x ^ (p - 1))))
          = jacWeight p c * jacAnti T p c - jacWeight p ε * jacAnti T p ε
            - ∫ x in ε..c, jacWeight' p x * jacAnti T p x :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := jacWeight p) (v := jacAnti T p)
        (u' := jacWeight' p)
        (v' := fun x => blockE T (x ^ p) * ((p : ℝ) * x ^ (p - 1)))
        hφderiv hAderiv hφ'int hA'int
    -- The IBP left side equals `∫_ε^c g` by the cancellation identity.
    have hlhs : (∫ x in ε..c, jacWeight p x * (blockE T (x ^ p) * ((p : ℝ) * x ^ (p - 1))))
        = ∫ x in ε..c, g x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hεc'] at hx
      exact jacWeight_mul_jacAnti_deriv hp1 T (lt_of_lt_of_le hε hx.1)
    -- The tail is `≤ 0`: `jacWeight'·A ≤ 0` pointwise on `(0,c]`.
    have htail_nonpos : (∫ x in ε..c, jacWeight' p x * jacAnti T p x) ≤ 0 := by
      have hle : (∫ x in ε..c, jacWeight' p x * jacAnti T p x) ≤ ∫ _ in ε..c, (0 : ℝ) := by
        apply intervalIntegral.integral_mono_on hεc'
        · -- integrability of the tail on [ε,c]
          apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.mul
          · apply ContinuousOn.mul continuousOn_const
            apply ContinuousOn.rpow_const continuousOn_id
            intro x hx; left
            rw [Set.uIcc_of_le hεc'] at hx
            exact ne_of_gt (lt_of_lt_of_le hε hx.1)
          · unfold jacAnti
            exact ((continuous_blockRun T).comp (continuous_pow p)).continuousOn
        · exact _root_.intervalIntegrable_const
        · intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
          have hxIcc : x ^ p ∈ Icc (0:ℝ) 1 := by
            refine ⟨by positivity, ?_⟩
            have hxc : x ≤ c := hx.2
            have hx1 : x ≤ 1 := le_trans hxc hc.2
            exact pow_le_one₀ hx0.le hx1
          have hAx : 0 ≤ jacAnti T p x := by
            unfold jacAnti; exact blockRun_nonneg hT hxIcc
          have hφ'x : jacWeight' p x ≤ 0 := by
            unfold jacWeight'
            have h1 : ((1 : ℝ) - p) / p ≤ 0 := by
              apply div_nonpos_of_nonpos_of_nonneg
              · linarith
              · positivity
            have h2 : 0 ≤ x ^ ((-p : ℝ)) := Real.rpow_nonneg hx0.le _
            exact mul_nonpos_of_nonpos_of_nonneg h1 h2
          exact mul_nonpos_of_nonpos_of_nonneg hφ'x hAx
      simpa using hle
    -- Assemble: `∫_ε^c g = φ(c)A(c) − φ(ε)A(ε) − tail ≥ φ(c)A(c) − φ(ε)A(ε)`.
    rw [hlhs] at hIBP
    unfold jacAnti at hIBP htail_nonpos
    linarith [hIBP, htail_nonpos]
  -- Lower boundary `φ(ε)·A(ε) → 0` as `ε ↓ 0`, via the growth bound.
  obtain ⟨M, hM0, hMbound⟩ := abs_blockRun_le T
  -- `|φ(ε)·A(ε)| ≤ (M/p)·ε` for `ε ∈ (0,1]`.
  have hφεAε_bound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |jacWeight p ε * blockRun T (ε ^ p)| ≤ (M / p) * ε := by
    intro ε hε hε1
    have hεp_mem : ε ^ p ∈ Icc (0:ℝ) 1 :=
      ⟨by positivity, pow_le_one₀ hε.le hε1⟩
    have hAbound : |blockRun T (ε ^ p)| ≤ M * ε ^ p := hMbound _ hεp_mem
    have hφε : jacWeight p ε = ε ^ ((1:ℝ) - p) / p := rfl
    rw [hφε, abs_mul]
    have hφabs : |ε ^ ((1:ℝ) - p) / p| = ε ^ ((1:ℝ) - p) / p := by
      rw [abs_of_nonneg]
      have : 0 ≤ ε ^ ((1:ℝ) - p) := Real.rpow_nonneg hε.le _
      positivity
    rw [hφabs]
    -- (ε^{1-p}/p)·|A| ≤ (ε^{1-p}/p)·(M·ε^p) = (M/p)·ε^{1-p+p} = (M/p)·ε.
    calc ε ^ ((1:ℝ) - p) / p * |blockRun T (ε ^ p)|
        ≤ ε ^ ((1:ℝ) - p) / p * (M * ε ^ p) := by
          apply mul_le_mul_of_nonneg_left hAbound
          have : 0 ≤ ε ^ ((1:ℝ) - p) := Real.rpow_nonneg hε.le _
          positivity
      _ = (M / p) * ε := by
          have hεpR : (ε : ℝ) ^ p = ε ^ (p : ℝ) := (Real.rpow_natCast ε p).symm
          have hmul : ε ^ ((1:ℝ) - p) * ε ^ (p : ℝ) = ε := by
            rw [← Real.rpow_add hε, show (1:ℝ) - ↑p + ↑p = (1:ℝ) by ring, Real.rpow_one]
          rw [hεpR]
          field_simp
          nlinarith [hmul]
  -- Goal: `φ(c)·A(c) ≤ ∫₀ᶜ g`.
  change jacWeight p c * blockRun T (c ^ p) ≤ ∫ u in (0:ℝ)..c, g u
  -- We pass to the limit `ε ↓ 0` of the lower bound from `hstep`.
  -- `∫₀ᶜ g = ∫₀^ε g + ∫_ε^c g`, so `∫₀ᶜ g ≥ φ(c)A(c) − φ(ε)A(ε) + ∫₀^ε g`.
  have hgint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hgcont.intervalIntegrable a b
  -- The function `ε ↦ ∫₀^ε g` is continuous at `0` with value `0`.
  have hprim0 : Filter.Tendsto (fun ε : ℝ => ∫ u in (0:ℝ)..ε, g u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hcontprim : ContinuousAt (fun ε : ℝ => ∫ u in (0:ℝ)..ε, g u) 0 :=
      (intervalIntegral.integral_hasDerivAt_right (hgint 0 0)
        (hgcont.stronglyMeasurableAtFilter _ _) hgcont.continuousAt).continuousAt
    have : Filter.Tendsto (fun ε : ℝ => ∫ u in (0:ℝ)..ε, g u)
        (nhds 0) (nhds (∫ u in (0:ℝ)..(0:ℝ), g u)) := hcontprim.tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  -- The lower boundary `φ(ε)·A(ε) → 0`.
  have hφεAε_tendsto : Filter.Tendsto (fun ε : ℝ => jacWeight p ε * blockRun T (ε ^ p))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro δ hδ
    refine ⟨min 1 (δ / (M / p + 1)), by positivity, ?_⟩
    intro ε hεIoi hεlt
    have hε : 0 < ε := hεIoi
    have hεlt' : ε < min 1 (δ / (M / p + 1)) := by
      rwa [Real.dist_eq, sub_zero, abs_of_pos hε] at hεlt
    have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hεlt' (min_le_left _ _))
    have hb := hφεAε_bound ε hε hε1
    rw [Real.dist_eq, sub_zero]
    have hεlt2 : ε < δ / (M / p + 1) :=
      lt_of_lt_of_le hεlt' (min_le_right _ _)
    have hMp1 : 0 < M / p + 1 := by positivity
    calc |jacWeight p ε * blockRun T (ε ^ p)| ≤ (M / p) * ε := hb
      _ ≤ (M / p + 1) * ε := by nlinarith [hε.le]
      _ < (M / p + 1) * (δ / (M / p + 1)) := by
          apply mul_lt_mul_of_pos_left hεlt2 hMp1
      _ = δ := by field_simp
  -- Combine: the constant `∫₀ᶜ g` dominates `φ(c)A(c) − φ(ε)A(ε) + ∫₀^ε g`,
  -- whose limit is `φ(c)A(c)`.
  have hlimit : Filter.Tendsto
      (fun ε : ℝ => jacWeight p c * blockRun T (c ^ p)
        - jacWeight p ε * blockRun T (ε ^ p) + ∫ u in (0:ℝ)..ε, g u)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (jacWeight p c * blockRun T (c ^ p))) := by
    have := ((tendsto_const_nhds (x := jacWeight p c * blockRun T (c ^ p))).sub
      hφεAε_tendsto).add hprim0
    simpa using this
  -- Eventually (for `0 < ε < c`) the quantity is `≤ ∫₀ᶜ g`.
  have hev : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      jacWeight p c * blockRun T (c ^ p) - jacWeight p ε * blockRun T (ε ^ p)
        + ∫ u in (0:ℝ)..ε, g u ≤ ∫ u in (0:ℝ)..c, g u := by
    have hIoo : Set.Ioo (0:ℝ) c ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT hc0
    filter_upwards [hIoo] with ε hε
    have hεpos : 0 < ε := hε.1
    have hεc : ε < c := hε.2
    have hsplit : (∫ u in (0:ℝ)..c, g u)
        = (∫ u in (0:ℝ)..ε, g u) + ∫ u in ε..c, g u :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hgint 0 ε) (hgint ε c)).symm
    have hs := hstep ε hεpos hεc
    rw [hsplit]
    linarith [hs]
  exact le_of_tendsto hlimit hev

/-- `blockRun T` is *strictly* positive on `(0,1]` for `T ⊆ {≥2}`. -/
theorem blockRun_pos {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {d : ℝ}
    (hd : d ∈ Ioc (0 : ℝ) 1) : 0 < blockRun T d :=
  blockE_partial_pos hT hd

/-- **The singular case `p ≥ 2` of running positivity under `u ↦ uᵖ`.**

Immediate from the boundary lower bound `bdry_le_running_comp_pow`, whose
left-hand side `φ(c)·A(c) ≥ 0`. -/
theorem running_pos_comp_pow_ge_two {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {p : ℕ}
    (hp2 : 2 ≤ p) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hc0 : 0 < c) :
    0 ≤ ∫ u in (0 : ℝ)..c, blockE T (u ^ p) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp2
  refine le_trans ?_ (bdry_le_running_comp_pow hT hp2 hc hc0)
  -- The boundary term `φ(c)·A(c) ≥ 0`.
  have hAc_nonneg : 0 ≤ blockRun T (c ^ p) :=
    blockRun_nonneg hT ⟨by positivity, pow_le_one₀ hc.1 hc.2⟩
  have hφc_nonneg : 0 ≤ jacWeight p c := by
    unfold jacWeight
    have : 0 ≤ c ^ ((1 : ℝ) - p) := Real.rpow_nonneg hc.1 _
    positivity
  exact mul_nonneg hφc_nonneg hAc_nonneg

/-- **Running positivity is preserved under `u ↦ uᵖ`.**

For a block support `T ⊆ {≥2}`, a prime power `p ≥ 1`, and any `c ∈ [0,1]`,

  `0 ≤ ∫₀ᶜ blockE T (uᵖ) du`.

This is the composed-integrand analogue of `blockE_partial_pos`, and is exactly
the running-integral hypothesis needed to run the weighted IBP engine with the
genuine block argument `uᵖ`. -/
theorem running_pos_comp_pow {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {p : ℕ}
    (hp : 1 ≤ p) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    0 ≤ ∫ u in (0 : ℝ)..c, blockE T (u ^ p) := by
  -- Reduce to `c > 0`; the case `c = 0` is trivial.
  rcases eq_or_lt_of_le hc.1 with hc0 | hc0
  · simp [← hc0]
  -- It suffices to show the running integral equals a nonnegative quantity.
  -- We split into `p = 1` (no singularity) and `p ≥ 2` (singular weight, ε-limit).
  rcases Nat.lt_or_ge p 2 with hp1 | hp2
  · -- `p = 1`: `uᵖ = u`, so this is `blockRun_nonneg` directly.
    interval_cases p
    · simpa [blockRun] using blockRun_nonneg hT hc
  · -- `p ≥ 2`: the genuine singular case.
    exact running_pos_comp_pow_ge_two hT hp2 hc hc0

/-- **Strict running positivity under `u ↦ uᵖ` on `(0,1]`.**

For `c ∈ (0,1]` the composed running integral is strictly positive.

* `p = 1`: directly `∫₀ᶜ blockE T u = blockRun T c > 0` (`blockRun_pos`).
* `p ≥ 2`: the boundary bound `bdry_le_running_comp_pow` dominates the integral
  below by `φ(c)·A(c) = (c^{1-p}/p)·blockRun T(cᵖ)`, which is strictly positive
  since `c > 0` (so `φ(c) > 0`) and `cᵖ ∈ (0,1]` (so `blockRun T(cᵖ) > 0`). -/
theorem running_pos_comp_pow_pos {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {p : ℕ}
    (hp : 1 ≤ p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..c, blockE T (u ^ p) := by
  have hc0 : 0 < c := hc.1
  have hc1 : c ≤ 1 := hc.2
  rcases Nat.lt_or_ge p 2 with hp1 | hp2
  · -- `p = 1`: `uᵖ = u`, so this is `blockRun_pos` directly.
    interval_cases p
    · simpa [blockRun] using blockRun_pos hT hc
  · -- `p ≥ 2`: strict positivity of the boundary term `φ(c)·A(c)`.
    refine lt_of_lt_of_le ?_ (bdry_le_running_comp_pow hT hp2 ⟨hc0.le, hc1⟩ hc0)
    -- `cᵖ ∈ (0,1]`, so `blockRun T(cᵖ) > 0`.
    have hcp_mem : c ^ p ∈ Ioc (0 : ℝ) 1 :=
      ⟨by positivity, pow_le_one₀ hc0.le hc1⟩
    have hAc_pos : 0 < blockRun T (c ^ p) := blockRun_pos hT hcp_mem
    have hφc_pos : 0 < jacWeight p c := by
      unfold jacWeight
      have : 0 < c ^ ((1 : ℝ) - p) := Real.rpow_pos_of_pos hc0 _
      positivity
    exact mul_pos hφc_pos hAc_pos

end ProductInvariants
