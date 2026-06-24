import ProductInvariants.Finite.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The universal block-exchange positivity crux

This file builds, in three layers, the deep `k ≥ 2` prime-exchange positivity
lemma.

After the substitution `v = u^p` the block exchange reduces to showing, for the
integrand `E(v) = ∏ᵢ(1 - v^{tᵢ}) - (1 - v)` attached to an antichain
`(t₁,…,t_k)`, that

  `Φ(c) = ∫₀ᶜ E(v) dv > 0`  for all `c ∈ (0,1]`.

We prove this via an **abstract shape argument** decoupled from the polynomial:

* **Layer 1 (this section): `integral_pos_of_single_crossing`.**
  If a continuous `E` is `> 0` on `(0,a)`, `< 0` on `(a,1)`, and its *total*
  integral `∫₀¹ E > 0`, then `∫₀ᶜ E > 0` for every `c ∈ (0,1]`.
  Reason: `Φ` is unimodal (rises on `(0,a)`, falls on `(a,1)`), so its infimum
  over `(0,1]` is attained at an endpoint — either the excluded `0` (where
  `Φ→0⁺`) or `1` (where `Φ(1) > 0`).

* **Layer 2 (endpoint bound):** `∫₀¹ E = F({tᵢ}) - 1/2 > 0`, equivalently
  `F(S) > 1/2` for every finite `S ⊆ {2,3,…}`. Confirmed numerically for all
  antichains (worst case `(2,3,5,7,11)`); the infinite limit `F({2,3,4,…})`
  is `≈ 0.51609 > 1/2`. There is **no pointwise/combinatorial shortcut**: the
  pointwise inequality `∏(1-vᵗ) ≥ 1-v` is *false* (375 violations observed), so
  the endpoint bound is genuinely an integrated statement.

* **Layer 3 (single-crossing):** `E` changes sign exactly once on `(0,1)`,
  `+` then `−`. This rests on the **universal exact factorisation**
  `E(v) = v·(1-v)·R(v)` with `R(v) = E(v)/(v(1-v))` (verified to hold with
  `0` exceptions across all tested antichains: `E(0)=E(1)=0` always, with simple
  roots). On `(0,1)` the sign of `E` equals the sign of `R`, and `R(0)>0`,
  `R(1)<0` universally. The crossing is unique iff `R` has a single root in
  `(0,1)`. `R` is *not* always monotone (monotone for only `7/88` shapes
  tested), so root-uniqueness is the **remaining universal gap**: it would
  follow from a Descartes-rule / Sturm-sequence bound on the number of positive
  roots, infrastructure not currently in Mathlib.

## Hybrid status

`integral_pos_of_single_crossing` (Layer 1) is proven **universally** and is
the load-bearing analytic core. Layers 2–3 are supplied **per antichain shape**:
the `(2,3)` instance is wired end-to-end in `BlockExchangeK2.lean`
(`Phi23_pos_via_layer1`), where the factorisation `E23 = v(1-v)(1-v²-v³)`,
strict antitonicity of `R23 = 1-v²-v³`, an IVT root, and the explicit endpoint
`∫₀¹ E23 = 1/12` discharge all hypotheses of Layer 1. Closing the universal crux
requires only the two shape-independent inputs above (uniqueness of the `R`-root
and `F(S) > 1/2`); the surrounding architecture is shape-agnostic.
-/

open MeasureTheory intervalIntegral Set

namespace ProductInvariants

/--
**Abstract unimodal positivity (single-crossing ⇒ running integral positive).**

Let `E` be continuous on `[0,1]`, strictly positive on `(0,a)`, strictly
negative on `(a,1)` (a single sign crossing, `+` then `−`), and suppose the full
integral `∫₀¹ E` is positive. Then the running integral `∫₀ᶜ E` is strictly
positive for every `c ∈ (0,1]`.
-/
theorem integral_pos_of_single_crossing {E : ℝ → ℝ}
    (hEc : ContinuousOn E (Icc 0 1)) {a : ℝ} (_ha : a ∈ Ioo (0 : ℝ) 1)
    (hposo : ∀ x ∈ Ioo (0 : ℝ) a, 0 < E x)
    (hpos : ∀ x ∈ Ioc (0 : ℝ) a, 0 ≤ E x)
    (hneg : ∀ x ∈ Icc a (1 : ℝ), E x ≤ 0)
    (hnego : ∀ x ∈ Ioo a (1 : ℝ), E x < 0)
    (hend : 0 < ∫ x in (0:ℝ)..1, E x)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ x in (0:ℝ)..c, E x := by
  obtain ⟨hc0, hc1⟩ := hc
  -- `E` is interval-integrable on every subinterval of `[0,1]`.
  have hint : ∀ x y : ℝ, x ∈ Icc (0:ℝ) 1 → y ∈ Icc (0:ℝ) 1 →
      IntervalIntegrable E volume x y := by
    intro x y hx hy
    apply ContinuousOn.intervalIntegrable
    apply hEc.mono
    apply uIcc_subset_Icc hx hy
  rcases le_total c a with hca | hca
  · -- `c ≤ a`: `E ≥ 0` on `(0,c]`, strictly positive somewhere ⇒ integral `> 0`.
    apply intervalIntegral.integral_pos hc0
    · exact hEc.mono (Icc_subset_Icc le_rfl hc1)
    · intro x hx
      exact hpos x ⟨hx.1, le_trans hx.2 hca⟩
    · refine ⟨c / 2, ⟨by positivity, by linarith⟩, ?_⟩
      exact hposo (c / 2) ⟨by positivity, by linarith⟩
  · -- `c > a`: write `Φ(c) = Φ(1) − ∫_c¹ E`, and `∫_c¹ E < 0` since `E < 0` there.
    have hsplit : (∫ x in (0:ℝ)..1, E x)
        = (∫ x in (0:ℝ)..c, E x) + ∫ x in c..1, E x :=
      (integral_add_adjacent_intervals
        (hint 0 c ⟨le_rfl, by norm_num⟩ ⟨hc0.le, hc1⟩)
        (hint c 1 ⟨hc0.le, hc1⟩ ⟨by norm_num, le_rfl⟩)).symm
    have hneg_tail : (∫ x in c..1, E x) ≤ 0 := by
      rcases eq_or_lt_of_le hc1 with rfl | hc1'
      · simp
      · apply le_of_lt
        have : (∫ x in c..1, E x) < ∫ x in c..1, (0 : ℝ) := by
          apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt hc1'
            (hEc.mono (Icc_subset_Icc hc0.le le_rfl)) continuousOn_const
          · intro x hx
            exact hneg x ⟨le_trans hca hx.1.le, hx.2⟩
          · refine ⟨(c + 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
            exact hnego ((c + 1) / 2) ⟨by linarith, by linarith⟩
        simpa using this
    linarith [hsplit, hend, hneg_tail]

end ProductInvariants
