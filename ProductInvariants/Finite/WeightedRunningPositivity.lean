import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Weighted running-integral positivity (Abel / integration-by-parts)

This file proves the abstract analytic engine behind the deep block-exchange
descent.  The block exchange reduces (after the substitution `v = u^p`) to an
inequality of the form

  `∫₀¹ w(u) · g(u) du ≥ 0`,

where `g` has *nonnegative running integrals* `G(c) = ∫₀ᶜ g ≥ 0` (the universal
partial-positivity certificate `blockE_partial_pos`), and `w ≥ 0` is a
*decreasing* weight (a phase product `P[B]`, which is antitone in `u`).

The proof is integration by parts: with `G(x) = ∫₀ˣ g`,

  `∫₀¹ w·g = ∫₀¹ w·G' = w(1)G(1) − w(0)G(0) − ∫₀¹ w'·G`,

and `G(0)=0`, `w(1)G(1) ≥ 0`, `−w'·G ≥ 0` (since `w' ≤ 0`, `G ≥ 0`).

A strict variant is also provided.
-/

open MeasureTheory intervalIntegral Set

namespace ProductInvariants

/-- **Weighted running-integral positivity (IBP form).**

Let `g` be continuous, `w` differentiable with derivative `w'` on `[0,1]`, with
`w ≥ 0`, `w' ≤ 0` (so `w` is decreasing).  If the running integrals
`G(c) = ∫₀ᶜ g` are all nonnegative on `[0,1]`, then the weighted integral
`∫₀¹ w·g` is nonnegative. -/
theorem integral_weight_mul_nonneg
    {g w w' : ℝ → ℝ}
    (hg : Continuous g)
    (hw : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt w (w' x) x)
    (hw'int : IntervalIntegrable w' volume 0 1)
    (hwnonneg : 0 ≤ w 1)
    (hw'nonpos : ∀ x ∈ Icc (0 : ℝ) 1, w' x ≤ 0)
    (hG : ∀ c ∈ Icc (0 : ℝ) 1, 0 ≤ ∫ t in (0 : ℝ)..c, g t) :
    0 ≤ ∫ u in (0 : ℝ)..1, w u * g u := by
  -- `G x = ∫₀ˣ g`, the running integral; `G' = g` by FTC, `G 0 = 0`.
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t with hGdef
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hGderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt G (g x) x := by
    intro x _hx
    exact intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 x)
      (hg.stronglyMeasurableAtFilter _ _)
      hg.continuousAt
  -- `g` and `w'` are interval-integrable.
  have hgint : IntervalIntegrable g volume 0 1 := hg.intervalIntegrable 0 1
  -- Integration by parts: ∫ w·G' = w(1)G(1) − w(0)G(0) − ∫ w'·G.
  have hIBP :
      (∫ u in (0 : ℝ)..1, w u * g u) =
        w 1 * G 1 - w 0 * G 0 - ∫ u in (0 : ℝ)..1, w' u * G u := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := w) (v := G) (u' := w') (v' := g) hw hGderiv hw'int hgint
    simpa using h
  rw [hIBP, hG0]
  -- The boundary term `w(1)·G(1) ≥ 0`.
  have hbdry : 0 ≤ w 1 * G 1 :=
    mul_nonneg hwnonneg (hG 1 (by constructor <;> norm_num))
  -- The tail `−∫ w'·G ≥ 0` since `w'·G ≤ 0` pointwise on `[0,1]`.
  have htail : (∫ u in (0 : ℝ)..1, w' u * G u) ≤ 0 := by
    have hle : (∫ u in (0 : ℝ)..1, w' u * G u) ≤ ∫ u in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact hw'int.mul_continuousOn (by
          -- G is continuous on [0,1]
          have : ContinuousOn G (Icc (0:ℝ) 1) := by
            intro x hx
            exact ((hGderiv x (by rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hx)).continuousAt).continuousWithinAt
          simpa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using this)
      · exact _root_.intervalIntegrable_const
      · intro x hx
        have hx' : x ∈ Icc (0:ℝ) 1 := hx
        exact mul_nonpos_of_nonpos_of_nonneg (hw'nonpos x hx') (hG x hx')
    simpa using hle
  simp only [mul_zero, sub_zero]
  linarith

/-- **Strict weighted running-integral positivity (IBP form).**

Same hypotheses as `integral_weight_mul_nonneg`, but with *strict* running
positivity `G(c) > 0` on `(0,1]`, a continuous derivative `w'`, and a witness
point `x₀ ∈ (0,1)` where `w' x₀ < 0` (so the weight is genuinely decreasing).
Then `∫₀¹ w·g > 0`.

Note the boundary term `w(1)·G(1)` need not be used; strictness is supplied by
the tail `−∫₀¹ w'·G`, which is strictly positive because `w'·G < 0` near `x₀`. -/
theorem integral_weight_mul_pos
    {g w w' : ℝ → ℝ}
    (hg : Continuous g)
    (hw : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt w (w' x) x)
    (hw'cont : Continuous w')
    (hwnonneg : 0 ≤ w 1)
    (hw'nonpos : ∀ x ∈ Icc (0 : ℝ) 1, w' x ≤ 0)
    (hG : ∀ c ∈ Ioc (0 : ℝ) 1, 0 < ∫ t in (0 : ℝ)..c, g t)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hw'x₀ : w' x₀ < 0) :
    0 < ∫ u in (0 : ℝ)..1, w u * g u := by
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t with hGdef
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hGderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt G (g x) x := by
    intro x _hx
    exact intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 x)
      (hg.stronglyMeasurableAtFilter _ _)
      hg.continuousAt
  have hGcont : ContinuousOn G (Icc (0:ℝ) 1) := by
    intro x hx
    exact ((hGderiv x (by rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hx)).continuousAt).continuousWithinAt
  have hGnonneg : ∀ c ∈ Icc (0:ℝ) 1, 0 ≤ G c := by
    intro c hc
    rcases eq_or_lt_of_le hc.1 with h | h
    · simp [hGdef, ← h]
    · exact (hG c ⟨h, hc.2⟩).le
  have hgint : IntervalIntegrable g volume 0 1 := hg.intervalIntegrable 0 1
  have hw'int : IntervalIntegrable w' volume 0 1 := hw'cont.intervalIntegrable 0 1
  have hIBP :
      (∫ u in (0 : ℝ)..1, w u * g u) =
        w 1 * G 1 - w 0 * G 0 - ∫ u in (0 : ℝ)..1, w' u * G u := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := w) (v := G) (u' := w') (v' := g) hw hGderiv hw'int hgint
    simpa using h
  rw [hIBP, hG0]
  have hbdry : 0 ≤ w 1 * G 1 :=
    mul_nonneg hwnonneg (hGnonneg 1 (by constructor <;> norm_num))
  -- Strict tail: ∫ w'·G < 0.
  have htail : (∫ u in (0 : ℝ)..1, w' u * G u) < 0 := by
    have hlt : (∫ u in (0 : ℝ)..1, w' u * G u) < ∫ u in (0 : ℝ)..1, (0 : ℝ) := by
      apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
        ((hw'cont.continuousOn).mul hGcont) continuousOn_const
      · intro x hx
        have hx' : x ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hx
        exact mul_nonpos_of_nonpos_of_nonneg (hw'nonpos x hx') (hGnonneg x hx')
      · refine ⟨x₀, ?_, ?_⟩
        · exact ⟨hx₀.1.le, hx₀.2.le⟩
        · have hGx₀ : 0 < G x₀ := hG x₀ ⟨hx₀.1, hx₀.2.le⟩
          exact mul_neg_of_neg_of_pos hw'x₀ hGx₀
    simpa using hlt
  simp only [mul_zero, sub_zero]
  linarith

end ProductInvariants
