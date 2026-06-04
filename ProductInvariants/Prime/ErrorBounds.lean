import ProductInvariants.Finite.Monotonicity
import ProductInvariants.Finite.KernelCalculus

open MeasureTheory intervalIntegral

namespace ProductInvariants

lemma one_sub_prod_le_sum_one_sub {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h1a : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have ih' : 1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
        exact ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      have hp_le_one : ∏ i ∈ s, f i ≤ 1 := by
        have hprod : ∏ i ∈ s, f i ≤ ∏ i ∈ s, (1 : ℝ) := by
          exact Finset.prod_le_prod (s := s)
            (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
            (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
        simpa using hprod
      have hone_sub_p : 0 ≤ 1 - ∏ i ∈ s, f i := sub_nonneg.mpr hp_le_one
      have hmul :
          f a * (1 - ∏ i ∈ s, f i) ≤ 1 - ∏ i ∈ s, f i := by
        nlinarith
      calc
        1 - f a * (∏ i ∈ s, f i)
            = (1 - f a) + f a * (1 - ∏ i ∈ s, f i) := by ring
        _ ≤ (1 - f a) + (1 - ∏ i ∈ s, f i) := by linarith
        _ ≤ (1 - f a) + ∑ i ∈ s, (1 - f i) := by linarith

lemma phaseProduct_sdiff_mul {S T : Finset ℕ} (hST : S ⊆ T) (u : ℝ) :
    phaseProduct (T \ S) u * phaseProduct S u = phaseProduct T u := by
  simpa [phaseProduct] using
    (Finset.prod_sdiff (s₁ := S) (s₂ := T)
      (f := fun n => 1 - u ^ n) hST)

lemma loose_error_pointwise {S T : Finset ℕ} (hST : S ⊆ T) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    phaseProduct S u - phaseProduct T u ≤ ∑ q ∈ T \ S, u ^ q := by
  have hsd := phaseProduct_sdiff_mul hST u
  have hmain :
      phaseProduct S u - phaseProduct T u =
        phaseProduct S u * (1 - phaseProduct (T \ S) u) := by
    rw [← hsd]
    ring
  rw [hmain]
  have hprod :
      1 - phaseProduct (T \ S) u ≤ ∑ q ∈ T \ S, u ^ q := by
    unfold phaseProduct
    simpa [sub_eq_add_neg] using
      (one_sub_prod_le_sum_one_sub (T \ S) (fun q => 1 - u ^ q)
        (fun q _hq => one_sub_pow_nonneg_of_mem_Icc hu q)
        (fun q _hq => one_sub_pow_le_one_of_mem_Icc hu q))
  have hps0 : 0 ≤ phaseProduct S u := phaseProduct_nonneg_on_Icc S hu
  have hps1 : phaseProduct S u ≤ 1 := phaseProduct_le_one_on_Icc S hu
  have hsum0 : 0 ≤ ∑ q ∈ T \ S, u ^ q := by
    exact Finset.sum_nonneg (fun q _hq => pow_nonneg hu.1 q)
  nlinarith

theorem loose_error_bound {S T : Finset ℕ} (hST : S ⊆ T) :
    phaseIntegral S - phaseIntegral T ≤
      ∑ q ∈ T \ S, (1 : ℝ) / (q + 1) := by
  have hintSum :
      IntervalIntegrable (fun u : ℝ => ∑ q ∈ T \ S, u ^ q)
        volume (0 : ℝ) 1 := by
    exact (continuous_finset_sum (T \ S)
      (fun q _hq => continuous_id.pow q)).intervalIntegrable 0 1
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun u => phaseProduct S u - phaseProduct T u)
    (g := fun u => ∑ q ∈ T \ S, u ^ q)
    (by norm_num)
    ((intervalIntegrable_phaseProduct S).sub (intervalIntegrable_phaseProduct T))
    hintSum
    (fun _u hu => loose_error_pointwise hST hu)
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_phaseProduct S) (intervalIntegrable_phaseProduct T)] at hmono
  rw [intervalIntegral.integral_finset_sum] at hmono
  · have hsum :
        (∑ q ∈ T \ S, ∫ x in (0 : ℝ)..1, x ^ q) =
          ∑ q ∈ T \ S, (1 : ℝ) / (q + 1) := by
      refine Finset.sum_congr rfl ?_
      intro q _hq
      rw [integral_pow]
      norm_num
    rwa [hsum] at hmono
  · intro q _hq
    exact (continuous_id.pow q).intervalIntegrable 0 1

lemma sharp_error_pointwise {S T : Finset ℕ} (hST : S ⊆ T)
    (h2 : 2 ∈ S) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    phaseProduct S u - phaseProduct T u ≤
      ∑ q ∈ T \ S, (1 - u ^ 2) * u ^ q := by
  have hsd := phaseProduct_sdiff_mul hST u
  have hmain :
      phaseProduct S u - phaseProduct T u =
        phaseProduct S u * (1 - phaseProduct (T \ S) u) := by
    rw [← hsd]
    ring
  rw [hmain]
  have htail_le :
      1 - phaseProduct (T \ S) u ≤ ∑ q ∈ T \ S, u ^ q := by
    unfold phaseProduct
    simpa [sub_eq_add_neg] using
      (one_sub_prod_le_sum_one_sub (T \ S) (fun q => 1 - u ^ q)
        (fun q _hq => one_sub_pow_nonneg_of_mem_Icc hu q)
        (fun q _hq => one_sub_pow_le_one_of_mem_Icc hu q))
  have hpd_le : phaseProduct (T \ S) u ≤ 1 :=
    phaseProduct_le_one_on_Icc (T \ S) hu
  have htail0 : 0 ≤ 1 - phaseProduct (T \ S) u := sub_nonneg.mpr hpd_le
  have hps_le : phaseProduct S u ≤ 1 - u ^ 2 := by
    have hsub : {2} ⊆ S := by
      intro n hn
      have hn' : n = 2 := by simpa using hn
      simpa [hn'] using h2
    have hmono := phaseProduct_antitone hsub hu
    simpa [phaseProduct] using hmono
  have ha0 : 0 ≤ 1 - u ^ 2 := one_sub_pow_nonneg_of_mem_Icc hu 2
  have h1 :
      phaseProduct S u * (1 - phaseProduct (T \ S) u) ≤
        (1 - u ^ 2) * (1 - phaseProduct (T \ S) u) := by
    gcongr
  have h2le :
      (1 - u ^ 2) * (1 - phaseProduct (T \ S) u) ≤
        (1 - u ^ 2) * (∑ q ∈ T \ S, u ^ q) := by
    gcongr
  calc
    phaseProduct S u * (1 - phaseProduct (T \ S) u) ≤
        (1 - u ^ 2) * (1 - phaseProduct (T \ S) u) := h1
    _ ≤ (1 - u ^ 2) * (∑ q ∈ T \ S, u ^ q) := h2le
    _ = ∑ q ∈ T \ S, (1 - u ^ 2) * u ^ q := by
      rw [Finset.mul_sum]

lemma integral_one_sub_sq_mul_pow (q : ℕ) :
    (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * u ^ q) =
      (1 : ℝ) / (q + 1) - (1 : ℝ) / (q + 3) := by
  have hint1 :
      IntervalIntegrable (fun u : ℝ => u ^ q) volume (0 : ℝ) 1 :=
    (continuous_id.pow q).intervalIntegrable 0 1
  have hint2 :
      IntervalIntegrable (fun u : ℝ => u ^ (q + 2)) volume (0 : ℝ) 1 :=
    (continuous_id.pow (q + 2)).intervalIntegrable 0 1
  have hcongr :
      (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * u ^ q) =
        ∫ u in (0 : ℝ)..1, u ^ q - u ^ (q + 2) := by
    apply intervalIntegral.integral_congr
    intro u _hu
    ring
  rw [hcongr, intervalIntegral.integral_sub hint1 hint2, integral_pow, integral_pow]
  norm_num
  ring

lemma common_prefix_error_pointwise {R S T : Finset ℕ} (hRS : R ⊆ S) (hST : S ⊆ T)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    phaseProduct S u - phaseProduct T u ≤
      ∑ q ∈ T \ S, phaseProduct R u * u ^ q := by
  have hsd := phaseProduct_sdiff_mul hST u
  have hmain :
      phaseProduct S u - phaseProduct T u =
        phaseProduct S u * (1 - phaseProduct (T \ S) u) := by
    rw [← hsd]
    ring
  rw [hmain]
  have htail_le :
      1 - phaseProduct (T \ S) u ≤ ∑ q ∈ T \ S, u ^ q := by
    unfold phaseProduct
    simpa [sub_eq_add_neg] using
      (one_sub_prod_le_sum_one_sub (T \ S) (fun q => 1 - u ^ q)
        (fun q _hq => one_sub_pow_nonneg_of_mem_Icc hu q)
        (fun q _hq => one_sub_pow_le_one_of_mem_Icc hu q))
  have hpd_le : phaseProduct (T \ S) u ≤ 1 :=
    phaseProduct_le_one_on_Icc (T \ S) hu
  have htail0 : 0 ≤ 1 - phaseProduct (T \ S) u := sub_nonneg.mpr hpd_le
  have hps_le : phaseProduct S u ≤ phaseProduct R u :=
    phaseProduct_antitone hRS hu
  have hR0 : 0 ≤ phaseProduct R u := phaseProduct_nonneg_on_Icc R hu
  have h1 :
      phaseProduct S u * (1 - phaseProduct (T \ S) u) ≤
        phaseProduct R u * (1 - phaseProduct (T \ S) u) := by
    gcongr
  have h2le :
      phaseProduct R u * (1 - phaseProduct (T \ S) u) ≤
        phaseProduct R u * (∑ q ∈ T \ S, u ^ q) := by
    gcongr
  calc
    phaseProduct S u * (1 - phaseProduct (T \ S) u) ≤
        phaseProduct R u * (1 - phaseProduct (T \ S) u) := h1
    _ ≤ phaseProduct R u * (∑ q ∈ T \ S, u ^ q) := h2le
    _ = ∑ q ∈ T \ S, phaseProduct R u * u ^ q := by
      rw [Finset.mul_sum]

/--
Common-prefix finite error bound.

The linear and quadratic bounds are the special cases `R = ∅` and `R = {2}`.
-/
theorem common_prefix_error_bound {R S T : Finset ℕ} (hRS : R ⊆ S) (hST : S ⊆ T) :
    phaseIntegral S - phaseIntegral T ≤
      ∑ q ∈ T \ S, commonPrefixKernel R q := by
  have hintSum :
      IntervalIntegrable
        (fun u : ℝ => ∑ q ∈ T \ S, phaseProduct R u * u ^ q)
        volume (0 : ℝ) 1 := by
    exact (continuous_finset_sum (T \ S)
      (fun q _hq =>
        ((continuous_phaseProduct R).mul (continuous_id.pow q)))).intervalIntegrable 0 1
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun u => phaseProduct S u - phaseProduct T u)
    (g := fun u => ∑ q ∈ T \ S, phaseProduct R u * u ^ q)
    (by norm_num)
    ((intervalIntegrable_phaseProduct S).sub (intervalIntegrable_phaseProduct T))
    hintSum
    (fun _u hu => common_prefix_error_pointwise hRS hST hu)
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_phaseProduct S) (intervalIntegrable_phaseProduct T)] at hmono
  rw [intervalIntegral.integral_finset_sum] at hmono
  · simpa [commonPrefixKernel] using hmono
  · intro q _hq
    exact ((continuous_phaseProduct R).mul (continuous_id.pow q)).intervalIntegrable 0 1

theorem commonPrefixKernel_empty (q : ℕ) :
    commonPrefixKernel ∅ q = (1 : ℝ) / (q + 1) := by
  unfold commonPrefixKernel
  simp [phaseProduct, integral_pow]

theorem commonPrefixKernel_singleton_two (q : ℕ) :
    commonPrefixKernel ({2} : Finset ℕ) q =
      (1 : ℝ) / (q + 1) - (1 : ℝ) / (q + 3) := by
  unfold commonPrefixKernel
  simpa [phaseProduct, mul_comm, mul_left_comm, mul_assoc] using
    integral_one_sub_sq_mul_pow q

theorem commonPrefixKernel_pair_two_three (q : ℕ) :
    commonPrefixKernel ({2, 3} : Finset ℕ) q =
      (1 : ℝ) / (q + 1) - (1 : ℝ) / (q + 3) -
        (1 : ℝ) / (q + 4) + (1 : ℝ) / (q + 6) := by
  unfold commonPrefixKernel
  have hint1 : IntervalIntegrable (fun u : ℝ => u ^ q) volume (0 : ℝ) 1 :=
    (continuous_id.pow q).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun u : ℝ => u ^ (q + 2)) volume (0 : ℝ) 1 :=
    (continuous_id.pow (q + 2)).intervalIntegrable 0 1
  have hint3 : IntervalIntegrable (fun u : ℝ => u ^ (q + 3)) volume (0 : ℝ) 1 :=
    (continuous_id.pow (q + 3)).intervalIntegrable 0 1
  have hint4 : IntervalIntegrable (fun u : ℝ => u ^ (q + 5)) volume (0 : ℝ) 1 :=
    (continuous_id.pow (q + 5)).intervalIntegrable 0 1
  have hcongr :
      (∫ u in (0 : ℝ)..1, phaseProduct ({2, 3} : Finset ℕ) u * u ^ q) =
        ∫ u in (0 : ℝ)..1, ((u ^ q - u ^ (q + 2)) - u ^ (q + 3)) + u ^ (q + 5) := by
    apply intervalIntegral.integral_congr
    intro u _hu
    simp [phaseProduct]
    ring
  rw [hcongr]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_sub hint1 hint2]
      repeat rw [integral_pow]
      norm_num
      ring
    · exact hint1.sub hint2
    · exact hint3
  · exact (hint1.sub hint2).sub hint3
  · exact hint4

theorem sharp_error_bound {S T : Finset ℕ} (hST : S ⊆ T) (h2 : 2 ∈ S) :
    phaseIntegral S - phaseIntegral T ≤
      ∑ q ∈ T \ S,
        ((1 : ℝ) / (q + 1) - (1 : ℝ) / (q + 3)) := by
  have hintSum :
      IntervalIntegrable
        (fun u : ℝ => ∑ q ∈ T \ S, (1 - u ^ 2) * u ^ q)
        volume (0 : ℝ) 1 := by
    exact (continuous_finset_sum (T \ S)
      (fun q _hq =>
        ((continuous_const.sub (continuous_id.pow 2)).mul
          (continuous_id.pow q)))).intervalIntegrable 0 1
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun u => phaseProduct S u - phaseProduct T u)
    (g := fun u => ∑ q ∈ T \ S, (1 - u ^ 2) * u ^ q)
    (by norm_num)
    ((intervalIntegrable_phaseProduct S).sub (intervalIntegrable_phaseProduct T))
    hintSum
    (fun _u hu => sharp_error_pointwise hST h2 hu)
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_phaseProduct S) (intervalIntegrable_phaseProduct T)] at hmono
  rw [intervalIntegral.integral_finset_sum] at hmono
  · have hsum :
        (∑ q ∈ T \ S, ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * u ^ q) =
          ∑ q ∈ T \ S,
            ((1 : ℝ) / (q + 1) - (1 : ℝ) / (q + 3)) := by
      refine Finset.sum_congr rfl ?_
      intro q _hq
      rw [integral_one_sub_sq_mul_pow]
    rwa [hsum] at hmono
  · intro q _hq
    exact (((continuous_const.sub (continuous_id.pow 2)).mul
      (continuous_id.pow q))).intervalIntegrable 0 1

theorem sharp_error_bound_two_over {S T : Finset ℕ}
    (hST : S ⊆ T) (h2 : 2 ∈ S) :
    phaseIntegral S - phaseIntegral T ≤
      ∑ q ∈ T \ S,
        (2 : ℝ) / ((q + 1) * (q + 3)) := by
  have h := sharp_error_bound hST h2
  have hsum :
      (∑ q ∈ T \ S,
        ((1 : ℝ) / (q + 1) - (1 : ℝ) / (q + 3))) =
      ∑ q ∈ T \ S,
        (2 : ℝ) / ((q + 1) * (q + 3)) := by
    refine Finset.sum_congr rfl ?_
    intro q _hq
    field_simp
    ring
  rwa [hsum] at h

end ProductInvariants
