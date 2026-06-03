import ProductInvariants.Finite.PhaseMetric

open MeasureTheory Set

namespace ProductInvariants

private theorem weighted_covariance_expand
    {w f g : ℝ → ℝ} {c₁ c₂ : ℝ}
    (hw : Continuous w) (hf : Continuous f) (hg : Continuous g) :
    ∫ x in (0 : ℝ)..1, w x * ((f x - c₁) * (g x - c₂)) =
      (∫ x in (0 : ℝ)..1, w x * (f x * g x)) -
      c₁ * (∫ x in (0 : ℝ)..1, w x * g x) -
      c₂ * (∫ x in (0 : ℝ)..1, w x * f x) +
      c₁ * c₂ * (∫ x in (0 : ℝ)..1, w x) := by
  have h_wfg :
      IntervalIntegrable (fun x => w x * (f x * g x)) volume 0 1 :=
    (hw.mul (hf.mul hg)).intervalIntegrable 0 1
  have h_wg : IntervalIntegrable (fun x => w x * g x) volume 0 1 :=
    (hw.mul hg).intervalIntegrable 0 1
  have h_wf : IntervalIntegrable (fun x => w x * f x) volume 0 1 :=
    (hw.mul hf).intervalIntegrable 0 1
  have h_w : IntervalIntegrable w volume 0 1 :=
    hw.intervalIntegrable 0 1
  have h_eq :
      (fun x => w x * ((f x - c₁) * (g x - c₂))) =
        fun x =>
          w x * (f x * g x) +
          ((-c₁) * (w x * g x) +
          ((-c₂) * (w x * f x) + (c₁ * c₂) * w x)) := by
    ext x
    ring
  rw [h_eq]
  rw [show
      (fun x =>
          w x * (f x * g x) +
          ((-c₁) * (w x * g x) +
          ((-c₂) * (w x * f x) + (c₁ * c₂) * w x))) =
        fun x =>
          (fun x => w x * (f x * g x)) x +
          (fun x =>
            (-c₁) * (w x * g x) +
            ((-c₂) * (w x * f x) + (c₁ * c₂) * w x)) x from rfl]
  rw [intervalIntegral.integral_add h_wfg
    ((h_wg.const_mul (-c₁)).add ((h_wf.const_mul (-c₂)).add (h_w.const_mul (c₁ * c₂))))]
  rw [show
      (fun x =>
          (-c₁) * (w x * g x) +
          ((-c₂) * (w x * f x) + (c₁ * c₂) * w x)) =
        fun x =>
          (fun x => (-c₁) * (w x * g x)) x +
          (fun x => (-c₂) * (w x * f x) + (c₁ * c₂) * w x) x from rfl]
  rw [intervalIntegral.integral_add (h_wg.const_mul (-c₁))
    ((h_wf.const_mul (-c₂)).add (h_w.const_mul (c₁ * c₂)))]
  rw [show
      (fun x => (-c₂) * (w x * f x) + (c₁ * c₂) * w x) =
        fun x =>
          (fun x => (-c₂) * (w x * f x)) x +
          (fun x => (c₁ * c₂) * w x) x from rfl]
  rw [intervalIntegral.integral_add (h_wf.const_mul (-c₂)) (h_w.const_mul (c₁ * c₂))]
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Weighted Chebyshev inequality on `[0,1]`.

The weight is assumed nonnegative. This is the positive-association step behind
the phase-polymatroid inequality. -/
theorem chebyshev_integral_antitone_weighted
    {w f g : ℝ → ℝ}
    (hw_cont : Continuous w) (hf_cont : Continuous f) (hg_cont : Continuous g)
    (hw_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ w x)
    (hf_anti : AntitoneOn f (Icc (0 : ℝ) 1))
    (hg_anti : AntitoneOn g (Icc (0 : ℝ) 1)) :
    (∫ x in (0 : ℝ)..1, w x * f x) *
        (∫ y in (0 : ℝ)..1, w y * g y) ≤
      (∫ x in (0 : ℝ)..1, w x) *
        (∫ u in (0 : ℝ)..1, w u * (f u * g u)) := by
  set W := ∫ x in (0 : ℝ)..1, w x
  set Wf := ∫ x in (0 : ℝ)..1, w x * f x
  set Wg := ∫ x in (0 : ℝ)..1, w x * g x
  set Wfg := ∫ x in (0 : ℝ)..1, w x * (f x * g x)
  have h_inner_nonneg : ∀ y ∈ Icc (0 : ℝ) 1,
      0 ≤ Wfg - f y * Wg - g y * Wf + f y * g y * W := by
    intro y hy
    have hcov :
        ∫ x in (0 : ℝ)..1, w x * ((f x - f y) * (g x - g y)) =
          Wfg - f y * Wg - g y * Wf + f y * g y * W := by
      simpa [W, Wf, Wg, Wfg, mul_assoc] using
        weighted_covariance_expand (w := w) (f := f) (g := g)
          (c₁ := f y) (c₂ := g y) hw_cont hf_cont hg_cont
    have hnon :
        0 ≤ ∫ x in (0 : ℝ)..1, w x * ((f x - f y) * (g x - g y)) :=
      intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
        (fun x hx =>
          mul_nonneg (hw_nonneg x hx)
            (antitoneOn_covariance_nonneg hf_anti hg_anti hx hy))
    linarith
  have h_outer_nonneg :
      0 ≤ ∫ y in (0 : ℝ)..1,
        w y * (Wfg - f y * Wg - g y * Wf + f y * g y * W) :=
    intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (fun y hy =>
        mul_nonneg (hw_nonneg y hy) (h_inner_nonneg y hy))
  have h_outer :
      ∫ y in (0 : ℝ)..1,
        w y * (Wfg - f y * Wg - g y * Wf + f y * g y * W) =
          2 * (W * Wfg - Wf * Wg) := by
    have h_w : IntervalIntegrable w volume 0 1 :=
      hw_cont.intervalIntegrable 0 1
    have h_wf : IntervalIntegrable (fun y => w y * f y) volume 0 1 :=
      (hw_cont.mul hf_cont).intervalIntegrable 0 1
    have h_wg : IntervalIntegrable (fun y => w y * g y) volume 0 1 :=
      (hw_cont.mul hg_cont).intervalIntegrable 0 1
    have h_wfg : IntervalIntegrable (fun y => w y * (f y * g y)) volume 0 1 :=
      (hw_cont.mul (hf_cont.mul hg_cont)).intervalIntegrable 0 1
    have h_eq :
        (fun y => w y * (Wfg - f y * Wg - g y * Wf + f y * g y * W)) =
          fun y =>
            Wfg * w y +
            ((-Wg) * (w y * f y) +
            ((-Wf) * (w y * g y) + W * (w y * (f y * g y)))) := by
      ext y
      ring
    rw [h_eq]
    rw [show
        (fun y =>
            Wfg * w y +
            ((-Wg) * (w y * f y) +
            ((-Wf) * (w y * g y) + W * (w y * (f y * g y))))) =
          fun y =>
            (fun y => Wfg * w y) y +
            (fun y =>
              (-Wg) * (w y * f y) +
              ((-Wf) * (w y * g y) + W * (w y * (f y * g y)))) y from rfl]
    rw [intervalIntegral.integral_add (h_w.const_mul Wfg)
      ((h_wf.const_mul (-Wg)).add ((h_wg.const_mul (-Wf)).add (h_wfg.const_mul W)))]
    rw [show
        (fun y =>
            (-Wg) * (w y * f y) +
            ((-Wf) * (w y * g y) + W * (w y * (f y * g y)))) =
          fun y =>
            (fun y => (-Wg) * (w y * f y)) y +
            (fun y => (-Wf) * (w y * g y) + W * (w y * (f y * g y))) y from rfl]
    rw [intervalIntegral.integral_add (h_wf.const_mul (-Wg))
      ((h_wg.const_mul (-Wf)).add (h_wfg.const_mul W))]
    rw [show
        (fun y => (-Wf) * (w y * g y) + W * (w y * (f y * g y))) =
          fun y =>
            (fun y => (-Wf) * (w y * g y)) y +
            (fun y => W * (w y * (f y * g y))) y from rfl]
    rw [intervalIntegral.integral_add (h_wg.const_mul (-Wf)) (h_wfg.const_mul W)]
    simp only [intervalIntegral.integral_const_mul]
    ring
  linarith

private theorem productProfileP_disjoint_union
    {A B : Finset ℕ+} (hAB : Disjoint A B) (u : ℝ) :
    productProfileP (A ∪ B) u = productProfileP A u * productProfileP B u := by
  classical
  unfold productProfileP
  rw [Finset.prod_union hAB]

private theorem productProfileP_inter_sdiff_left (A B : Finset ℕ+) (u : ℝ) :
    productProfileP A u = productProfileP (A ∩ B) u * productProfileP (A \ B) u := by
  classical
  have hdisj : Disjoint (A ∩ B) (A \ B) := by
    rw [Finset.disjoint_left]
    intro x hxI hxD
    exact (Finset.mem_sdiff.mp hxD).2 (Finset.mem_inter.mp hxI).2
  have hunion : (A ∩ B) ∪ (A \ B) = A := by
    ext x
    by_cases hxB : x ∈ B <;> simp [hxB]
  calc
    productProfileP A u = productProfileP ((A ∩ B) ∪ (A \ B)) u := by rw [hunion]
    _ = productProfileP (A ∩ B) u * productProfileP (A \ B) u :=
      productProfileP_disjoint_union hdisj u

private theorem productProfileP_inter_sdiff_right (A B : Finset ℕ+) (u : ℝ) :
    productProfileP B u = productProfileP (A ∩ B) u * productProfileP (B \ A) u := by
  classical
  have hdisj : Disjoint (A ∩ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hxI hxD
    exact (Finset.mem_sdiff.mp hxD).2 (Finset.mem_inter.mp hxI).1
  have hunion : (A ∩ B) ∪ (B \ A) = B := by
    ext x
    by_cases hxA : x ∈ A <;> simp [hxA, and_comm]
  calc
    productProfileP B u = productProfileP ((A ∩ B) ∪ (B \ A)) u := by rw [hunion]
    _ = productProfileP (A ∩ B) u * productProfileP (B \ A) u :=
      productProfileP_disjoint_union hdisj u

private theorem productProfileP_union_inter_sdiff (A B : Finset ℕ+) (u : ℝ) :
    productProfileP (A ∪ B) u =
      productProfileP (A ∩ B) u * (productProfileP (A \ B) u * productProfileP (B \ A) u) := by
  classical
  unfold productProfileP
  have hdecomp : A ∪ B = (A ∩ B) ∪ ((A \ B) ∪ (B \ A)) := by
    ext x
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB]
  have hdisj1 : Disjoint (A ∩ B) ((A \ B) ∪ (B \ A)) := by
    rw [Finset.disjoint_left]
    intro x hxI hxU
    rcases Finset.mem_union.mp hxU with hxD | hxD
    · exact (Finset.mem_sdiff.mp hxD).2 (Finset.mem_inter.mp hxI).2
    · exact (Finset.mem_sdiff.mp hxD).2 (Finset.mem_inter.mp hxI).1
  have hdisj2 : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hxAB hxBA
    exact (Finset.mem_sdiff.mp hxAB).2 (Finset.mem_sdiff.mp hxBA).1
  rw [hdecomp, Finset.prod_union hdisj1, Finset.prod_union hdisj2]

/-- Finite phase-integrals are log-supermodular. Equivalently, the logarithmic
phase energy is submodular. -/
theorem phaseIntegralP_log_supermodular (A B : Finset ℕ+) :
    phaseIntegralP A * phaseIntegralP B ≤
      phaseIntegralP (A ∩ B) * phaseIntegralP (A ∪ B) := by
  classical
  let C := A ∩ B
  let X := A \ B
  let Y := B \ A
  have hcheb := chebyshev_integral_antitone_weighted
    (w := productProfileP C) (f := productProfileP X) (g := productProfileP Y)
    (continuous_productProfileP C) (continuous_productProfileP X) (continuous_productProfileP Y)
    (fun x hx => productProfileP_nonneg_on_Icc C hx)
    (productProfileP_antitoneOn X) (productProfileP_antitoneOn Y)
  have hA :
      (∫ u in (0 : ℝ)..1, productProfileP C u * productProfileP X u) =
        phaseIntegralP A := by
    unfold phaseIntegralP
    apply intervalIntegral.integral_congr
    intro u _hu
    simp only [C, X]
    exact (productProfileP_inter_sdiff_left A B u).symm
  have hB :
      (∫ u in (0 : ℝ)..1, productProfileP C u * productProfileP Y u) =
        phaseIntegralP B := by
    unfold phaseIntegralP
    apply intervalIntegral.integral_congr
    intro u _hu
    simp only [C, Y]
    exact (productProfileP_inter_sdiff_right A B u).symm
  have hC :
      (∫ u in (0 : ℝ)..1, productProfileP C u) =
        phaseIntegralP (A ∩ B) := by
    rfl
  have hU :
      (∫ u in (0 : ℝ)..1,
          productProfileP C u * (productProfileP X u * productProfileP Y u)) =
        phaseIntegralP (A ∪ B) := by
    unfold phaseIntegralP
    apply intervalIntegral.integral_congr
    intro u _hu
    simp only [C, X, Y]
    exact (productProfileP_union_inter_sdiff A B u).symm
  simpa [hA, hB, hC, hU] using hcheb

/-- The logarithmic phase energy is a normalized monotone submodular rank
function on finite positive-exponent sets. -/
theorem phaseEnergy_submodular (A B : Finset ℕ+) :
    phaseEnergy (A ∪ B) + phaseEnergy (A ∩ B) ≤
      phaseEnergy A + phaseEnergy B := by
  unfold phaseEnergy
  have hA := phaseIntegralP_pos A
  have hB := phaseIntegralP_pos B
  have hI := phaseIntegralP_pos (A ∩ B)
  have hU := phaseIntegralP_pos (A ∪ B)
  have hmul_pos : 0 < phaseIntegralP A * phaseIntegralP B := mul_pos hA hB
  have hsuper := phaseIntegralP_log_supermodular A B
  have hlog : Real.log (phaseIntegralP A * phaseIntegralP B) ≤
      Real.log (phaseIntegralP (A ∩ B) * phaseIntegralP (A ∪ B)) :=
    Real.log_le_log hmul_pos hsuper
  rw [Real.log_mul hA.ne' hB.ne', Real.log_mul hI.ne' hU.ne'] at hlog
  linarith

/-- The nonnegative polymatroid interaction gap. -/
noncomputable def phaseInteractionGap (A B : Finset ℕ+) : ℝ :=
  phaseEnergy A + phaseEnergy B - phaseEnergy (A ∩ B) - phaseEnergy (A ∪ B)

theorem phaseInteractionGap_nonneg (A B : Finset ℕ+) :
    0 ≤ phaseInteractionGap A B := by
  unfold phaseInteractionGap
  linarith [phaseEnergy_submodular A B]

/-- Conditional second interaction of inserting two exponents over a background
set. -/
noncomputable def conditionalPairInteraction
    (R : Finset ℕ+) (p q : ℕ+) : ℝ :=
  phaseEnergy (insert p R) + phaseEnergy (insert q R) -
    phaseEnergy R - phaseEnergy (insert p (insert q R))

theorem conditionalPairInteraction_nonneg
    (R : Finset ℕ+) {p q : ℕ+}
    (hp : p ∉ R) (hq : q ∉ R) (hpq : p ≠ q) :
    0 ≤ conditionalPairInteraction R p q := by
  classical
  have hI : insert p R ∩ insert q R = R := by
    ext x
    by_cases hxR : x ∈ R <;>
      by_cases hxp : x = p <;>
      by_cases hxq : x = q <;>
      simp [hxR, hxp, hxq, hp, hq, hpq.symm]
  have hU : insert p R ∪ insert q R = insert p (insert q R) := by
    ext x
    simp [or_left_comm]
  unfold conditionalPairInteraction
  have h := phaseEnergy_submodular (insert p R) (insert q R)
  rw [hI, hU] at h
  linarith

end ProductInvariants
