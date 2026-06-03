import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open MeasureTheory Set

namespace ProductInvariants

/-- For antitone functions, the covariance kernel has nonnegative sign. -/
theorem antitoneOn_covariance_nonneg {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : AntitoneOn f s) (hg : AntitoneOn g s)
    {x : ℝ} (hx : x ∈ s) {y : ℝ} (hy : y ∈ s) :
    0 ≤ (f x - f y) * (g x - g y) := by
  rcases le_total x y with hxy | hxy
  · exact mul_nonneg (sub_nonneg.mpr (hf hx hy hxy)) (sub_nonneg.mpr (hg hx hy hxy))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hy hx hxy))
      (sub_nonpos.mpr (hg hy hx hxy))

private theorem covariance_expand {f g : ℝ → ℝ} {c₁ c₂ : ℝ}
    (hfg : IntervalIntegrable (fun u => f u * g u) volume 0 1)
    (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    ∫ x in (0 : ℝ)..1, (f x - c₁) * (g x - c₂) =
      (∫ x in (0 : ℝ)..1, f x * g x) - c₁ * (∫ x in (0 : ℝ)..1, g x) -
      c₂ * (∫ x in (0 : ℝ)..1, f x) + c₁ * c₂ := by
  have h_eq : (fun x => (f x - c₁) * (g x - c₂)) =
      fun x => f x * g x + (-c₁ * g x + (-c₂ * f x + c₁ * c₂)) := by
    ext x
    ring
  have hi_neg_c1_g : IntervalIntegrable (fun x => -c₁ * g x) volume 0 1 :=
    hg.const_mul (-c₁)
  have hi_neg_c2_f_plus :
      IntervalIntegrable (fun x => -c₂ * f x + c₁ * c₂) volume 0 1 :=
    (hf.const_mul (-c₂)).add intervalIntegrable_const
  have hi_rest :
      IntervalIntegrable (fun x => -c₁ * g x + (-c₂ * f x + c₁ * c₂)) volume 0 1 :=
    hi_neg_c1_g.add hi_neg_c2_f_plus
  rw [h_eq]
  rw [show (fun x => f x * g x + (-c₁ * g x + (-c₂ * f x + c₁ * c₂))) =
      fun x => (fun x => f x * g x) x +
        (fun x => -c₁ * g x + (-c₂ * f x + c₁ * c₂)) x from rfl]
  rw [intervalIntegral.integral_add hfg hi_rest]
  rw [show (fun x => -c₁ * g x + (-c₂ * f x + c₁ * c₂)) =
      fun x => (fun x => -c₁ * g x) x + (fun x => -c₂ * f x + c₁ * c₂) x from rfl]
  rw [intervalIntegral.integral_add hi_neg_c1_g hi_neg_c2_f_plus]
  rw [show (fun x => -c₂ * f x + c₁ * c₂) =
      fun x => (fun x => -c₂ * f x) x + (fun _ => c₁ * c₂) x from rfl]
  rw [intervalIntegral.integral_add (hf.const_mul (-c₂)) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul]
  ring

/-- Chebyshev's integral inequality for antitone functions on `[0,1]`. -/
theorem chebyshev_integral_antitone
    {f g : ℝ → ℝ}
    (hf_anti : AntitoneOn f (Icc 0 1))
    (hg_anti : AntitoneOn g (Icc 0 1))
    (hf_int : IntervalIntegrable f volume 0 1)
    (hg_int : IntervalIntegrable g volume 0 1)
    (hfg_int : IntervalIntegrable (fun u => f u * g u) volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x) * (∫ y in (0 : ℝ)..1, g y) ≤
      ∫ u in (0 : ℝ)..1, f u * g u := by
  set If := ∫ x in (0 : ℝ)..1, f x
  set Ig := ∫ x in (0 : ℝ)..1, g x
  set Ifg := ∫ x in (0 : ℝ)..1, f x * g x
  have hG_nonneg : ∀ y ∈ Icc (0 : ℝ) 1,
      0 ≤ Ifg - f y * Ig - g y * If + f y * g y := by
    intro y hy
    have hcov : ∫ x in (0 : ℝ)..1, (f x - f y) * (g x - g y) =
        Ifg - f y * Ig - g y * If + f y * g y :=
      covariance_expand hfg_int hf_int hg_int
    linarith [intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (fun x hx => antitoneOn_covariance_nonneg hf_anti hg_anti hx hy)]
  have h_int_G : ∫ y in (0 : ℝ)..1, (Ifg - f y * Ig - g y * If + f y * g y) =
      2 * (Ifg - If * Ig) := by
    have h_eq : (fun y => Ifg - f y * Ig - g y * If + f y * g y) =
        fun y => Ifg + (-Ig * f y + (-If * g y + f y * g y)) := by
      ext y
      ring
    have hi1 : IntervalIntegrable (fun _ : ℝ => Ifg) volume 0 1 := intervalIntegrable_const
    have hi2 : IntervalIntegrable (fun y => -Ig * f y) volume 0 1 := hf_int.const_mul (-Ig)
    have hi3_4 : IntervalIntegrable (fun y => -If * g y + f y * g y) volume 0 1 :=
      (hg_int.const_mul (-If)).add hfg_int
    have hi234 :
        IntervalIntegrable (fun y => -Ig * f y + (-If * g y + f y * g y)) volume 0 1 :=
      hi2.add hi3_4
    conv_lhs => rw [h_eq]
    rw [show (fun y => Ifg + (-Ig * f y + (-If * g y + f y * g y))) =
        fun y => (fun _ => Ifg) y +
          (fun y => -Ig * f y + (-If * g y + f y * g y)) y from rfl,
      intervalIntegral.integral_add hi1 hi234,
      show (fun y => -Ig * f y + (-If * g y + f y * g y)) =
        fun y => (fun y => -Ig * f y) y + (fun y => -If * g y + f y * g y) y from rfl,
      intervalIntegral.integral_add hi2 hi3_4,
      show (fun y => -If * g y + f y * g y) =
        fun y => (fun y => -If * g y) y + (fun y => f y * g y) y from rfl,
      intervalIntegral.integral_add (hg_int.const_mul (-If)) hfg_int]
    simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      smul_eq_mul]
    ring
  have h_ge :
      0 ≤ ∫ y in (0 : ℝ)..1, (Ifg - f y * Ig - g y * If + f y * g y) :=
    intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hG_nonneg
  linarith [h_int_G]

end ProductInvariants
