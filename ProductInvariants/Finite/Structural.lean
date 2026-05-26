import ProductInvariants.Prime.ErrorBounds
import Mathlib.Data.Finset.SymmDiff

open MeasureTheory intervalIntegral
open scoped symmDiff

namespace ProductInvariants

/-- The prefix of a finite exponent set through `N`. -/
def finitePrefix (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  S.filter fun q => q ≤ N

/-- The finite tail of an exponent set above `N`. -/
def finiteTail (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  S.filter fun q => N < q

@[simp]
theorem mem_finitePrefix {S : Finset ℕ} {N q : ℕ} :
    q ∈ finitePrefix S N ↔ q ∈ S ∧ q ≤ N := by
  simp [finitePrefix]

@[simp]
theorem mem_finiteTail {S : Finset ℕ} {N q : ℕ} :
    q ∈ finiteTail S N ↔ q ∈ S ∧ N < q := by
  simp [finiteTail]

theorem finitePrefix_subset (S : Finset ℕ) (N : ℕ) :
    finitePrefix S N ⊆ S := by
  intro q hq
  exact (mem_finitePrefix.mp hq).1

theorem finitePrefix_sdiff_eq_finiteTail (S : Finset ℕ) (N : ℕ) :
    S \ finitePrefix S N = finiteTail S N := by
  ext q
  by_cases hqS : q ∈ S
  · by_cases hqN : q ≤ N
    · simp [finiteTail, hqS, hqN, Nat.not_lt.mpr hqN]
    · have hNq : N < q := Nat.lt_of_not_ge hqN
      simp [finiteTail, hqS, hqN, hNq]
  · simp [finiteTail, hqS]

/--
Finite prefix stability with the sharp quadratic kernel.

Adding the finite tail above `N` can only decrease the phase integral, and if
the prefix already contains `2`, the drop is controlled by the square-tail
kernel over the omitted exponents.
-/
theorem finite_prefix_stability_sharp {S : Finset ℕ} {N : ℕ}
    (h2 : 2 ∈ finitePrefix S N) :
    0 ≤ phaseIntegral (finitePrefix S N) - phaseIntegral S ∧
      phaseIntegral (finitePrefix S N) - phaseIntegral S ≤
        ∑ q ∈ finiteTail S N, (2 : ℝ) / ((q + 1) * (q + 3)) := by
  have hsub := finitePrefix_subset S N
  constructor
  · exact sub_nonneg.mpr (phaseIntegral_antitone hsub)
  · simpa [finitePrefix_sdiff_eq_finiteTail] using
      sharp_error_bound_two_over (S := finitePrefix S N) (T := S) hsub h2

/-- Finite prefix stability with the coarse harmonic kernel. -/
theorem finite_prefix_stability_loose (S : Finset ℕ) (N : ℕ) :
    0 ≤ phaseIntegral (finitePrefix S N) - phaseIntegral S ∧
      phaseIntegral (finitePrefix S N) - phaseIntegral S ≤
        ∑ q ∈ finiteTail S N, (1 : ℝ) / (q + 1) := by
  have hsub := finitePrefix_subset S N
  constructor
  · exact sub_nonneg.mpr (phaseIntegral_antitone hsub)
  · simpa [finitePrefix_sdiff_eq_finiteTail] using
      loose_error_bound (S := finitePrefix S N) (T := S) hsub

/-- The sharp finite symmetric-difference distance. -/
noncomputable def sharpSymmDiffDist (S T : Finset ℕ) : ℝ :=
  ∑ q ∈ S ∆ T, (2 : ℝ) / ((q + 1) * (q + 3))

/-- The coarse finite symmetric-difference distance. -/
noncomputable def looseSymmDiffDist (S T : Finset ℕ) : ℝ :=
  ∑ q ∈ S ∆ T, (1 : ℝ) / (q + 1)

/-- Symmetric-difference distance induced by a common prefix kernel. -/
noncomputable def commonPrefixSymmDiffDist (R S T : Finset ℕ) : ℝ :=
  ∑ q ∈ S ∆ T, commonPrefixKernel R q

theorem sharpSymmDiffDist_nonneg (S T : Finset ℕ) :
    0 ≤ sharpSymmDiffDist S T := by
  unfold sharpSymmDiffDist
  exact Finset.sum_nonneg (fun q _hq => by positivity)

theorem looseSymmDiffDist_nonneg (S T : Finset ℕ) :
    0 ≤ looseSymmDiffDist S T := by
  unfold looseSymmDiffDist
  exact Finset.sum_nonneg (fun q _hq => by positivity)

theorem commonPrefixKernel_nonneg (R : Finset ℕ) (q : ℕ) :
    0 ≤ commonPrefixKernel R q := by
  unfold commonPrefixKernel
  exact intervalIntegral.integral_nonneg (by norm_num)
    (fun _u hu => mul_nonneg (phaseProduct_nonneg_on_Icc R hu) (pow_nonneg hu.1 q))

theorem commonPrefixSymmDiffDist_nonneg (R S T : Finset ℕ) :
    0 ≤ commonPrefixSymmDiffDist R S T := by
  unfold commonPrefixSymmDiffDist
  exact Finset.sum_nonneg (fun q _hq => commonPrefixKernel_nonneg R q)

lemma sum_kernel_le_sum_symmDiff_left (S T : Finset ℕ) :
    (∑ q ∈ S \ T, (2 : ℝ) / ((q + 1) * (q + 3))) ≤
      sharpSymmDiffDist S T := by
  unfold sharpSymmDiffDist
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.symmDiff_subset_sdiff
    (by
      intro q _hq _hqnot
      positivity)

lemma sum_kernel_le_sum_symmDiff_right (S T : Finset ℕ) :
    (∑ q ∈ T \ S, (2 : ℝ) / ((q + 1) * (q + 3))) ≤
      sharpSymmDiffDist S T := by
  unfold sharpSymmDiffDist
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.symmDiff_subset_sdiff'
    (by
      intro q _hq _hqnot
      positivity)

lemma sum_loose_kernel_le_sum_symmDiff_left (S T : Finset ℕ) :
    (∑ q ∈ S \ T, (1 : ℝ) / (q + 1)) ≤ looseSymmDiffDist S T := by
  unfold looseSymmDiffDist
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.symmDiff_subset_sdiff
    (by
      intro q _hq _hqnot
      positivity)

lemma sum_loose_kernel_le_sum_symmDiff_right (S T : Finset ℕ) :
    (∑ q ∈ T \ S, (1 : ℝ) / (q + 1)) ≤ looseSymmDiffDist S T := by
  unfold looseSymmDiffDist
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.symmDiff_subset_sdiff'
    (by
      intro q _hq _hqnot
      positivity)

lemma sum_commonPrefixKernel_le_sum_symmDiff_left (R S T : Finset ℕ) :
    (∑ q ∈ S \ T, commonPrefixKernel R q) ≤ commonPrefixSymmDiffDist R S T := by
  unfold commonPrefixSymmDiffDist
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.symmDiff_subset_sdiff
    (by
      intro q _hq _hqnot
      exact commonPrefixKernel_nonneg R q)

lemma sum_commonPrefixKernel_le_sum_symmDiff_right (R S T : Finset ℕ) :
    (∑ q ∈ T \ S, commonPrefixKernel R q) ≤ commonPrefixSymmDiffDist R S T := by
  unfold commonPrefixSymmDiffDist
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.symmDiff_subset_sdiff'
    (by
      intro q _hq _hqnot
      exact commonPrefixKernel_nonneg R q)

/--
Common-prefix Lipschitz bound.

If `R` is contained in the common core of `S` and `T`, then the symmetric
difference is measured with the stronger kernel obtained by multiplying by
`phaseProduct R`.
-/
theorem phaseIntegral_lipschitz_commonPrefix {R S T : Finset ℕ}
    (hR : R ⊆ S ∩ T) :
    |phaseIntegral S - phaseIntegral T| ≤ commonPrefixSymmDiffDist R S T := by
  rw [abs_sub_le_iff]
  constructor
  · have hS_union : S ⊆ S ∪ T := Finset.subset_union_left
    have hR_S : R ⊆ S := fun q hq => (Finset.mem_inter.mp (hR hq)).1
    have hcommon :
        phaseIntegral S - phaseIntegral (S ∪ T) ≤
          ∑ q ∈ (S ∪ T) \ S, commonPrefixKernel R q :=
      common_prefix_error_bound hR_S hS_union
    have hTu : phaseIntegral (S ∪ T) ≤ phaseIntegral T :=
      phaseIntegral_antitone Finset.subset_union_right
    have hdiff : phaseIntegral S - phaseIntegral T ≤
        phaseIntegral S - phaseIntegral (S ∪ T) := by linarith
    have hsum_eq :
        (∑ q ∈ (S ∪ T) \ S, commonPrefixKernel R q) =
          ∑ q ∈ T \ S, commonPrefixKernel R q := by
      refine Finset.sum_congr ?_ (fun q _ => rfl)
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨by
          rcases (Finset.mem_union.mp hq'.1) with hqS | hqT
          · exact False.elim (hq'.2 hqS)
          · exact hqT, hq'.2⟩
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right S hq'.1, hq'.2⟩
    exact hdiff.trans (hcommon.trans (by
      rw [hsum_eq]
      exact sum_commonPrefixKernel_le_sum_symmDiff_right R S T))
  · have hT_union : T ⊆ S ∪ T := Finset.subset_union_right
    have hR_T : R ⊆ T := fun q hq => (Finset.mem_inter.mp (hR hq)).2
    have hcommon :
        phaseIntegral T - phaseIntegral (S ∪ T) ≤
          ∑ q ∈ (S ∪ T) \ T, commonPrefixKernel R q :=
      common_prefix_error_bound hR_T hT_union
    have hSu : phaseIntegral (S ∪ T) ≤ phaseIntegral S :=
      phaseIntegral_antitone Finset.subset_union_left
    have hdiff : phaseIntegral T - phaseIntegral S ≤
        phaseIntegral T - phaseIntegral (S ∪ T) := by linarith
    have hsum_eq :
        (∑ q ∈ (S ∪ T) \ T, commonPrefixKernel R q) =
          ∑ q ∈ S \ T, commonPrefixKernel R q := by
      refine Finset.sum_congr ?_ (fun q _ => rfl)
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨by
          rcases (Finset.mem_union.mp hq'.1) with hqS | hqT
          · exact hqS
          · exact False.elim (hq'.2 hqT), hq'.2⟩
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left T hq'.1, hq'.2⟩
    exact hdiff.trans (hcommon.trans (by
      rw [hsum_eq]
      exact sum_commonPrefixKernel_le_sum_symmDiff_left R S T))

/--
Universal finite modulus of continuity.

If `2` lies in the common core, then the phase integral is 1-Lipschitz for the
weighted symmetric-difference distance.
-/
theorem phaseIntegral_lipschitz_sharp {S T : Finset ℕ}
    (h2 : 2 ∈ S ∩ T) :
    |phaseIntegral S - phaseIntegral T| ≤ sharpSymmDiffDist S T := by
  rw [abs_sub_le_iff]
  constructor
  · have hS_union : S ⊆ S ∪ T := Finset.subset_union_left
    have hsharp :
        phaseIntegral S - phaseIntegral (S ∪ T) ≤
          ∑ q ∈ (S ∪ T) \ S, (2 : ℝ) / ((q + 1) * (q + 3)) :=
      sharp_error_bound_two_over hS_union (by simpa using (Finset.mem_inter.mp h2).1)
    have hTu : phaseIntegral (S ∪ T) ≤ phaseIntegral T :=
      phaseIntegral_antitone Finset.subset_union_right
    have hdiff : phaseIntegral S - phaseIntegral T ≤
        phaseIntegral S - phaseIntegral (S ∪ T) := by linarith
    have hsum_eq :
        (∑ q ∈ (S ∪ T) \ S, (2 : ℝ) / ((q + 1) * (q + 3))) =
          ∑ q ∈ T \ S, (2 : ℝ) / ((q + 1) * (q + 3)) := by
      refine Finset.sum_congr ?_ (fun q _ => rfl)
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨by
          rcases (Finset.mem_union.mp hq'.1) with hqS | hqT
          · exact False.elim (hq'.2 hqS)
          · exact hqT, hq'.2⟩
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right S hq'.1, hq'.2⟩
    exact hdiff.trans (hsharp.trans (by
      rw [hsum_eq]
      exact sum_kernel_le_sum_symmDiff_right S T))
  · have hT_union : T ⊆ S ∪ T := Finset.subset_union_right
    have hsharp :
        phaseIntegral T - phaseIntegral (S ∪ T) ≤
          ∑ q ∈ (S ∪ T) \ T, (2 : ℝ) / ((q + 1) * (q + 3)) :=
      sharp_error_bound_two_over hT_union (by simpa using (Finset.mem_inter.mp h2).2)
    have hSu : phaseIntegral (S ∪ T) ≤ phaseIntegral S :=
      phaseIntegral_antitone Finset.subset_union_left
    have hdiff : phaseIntegral T - phaseIntegral S ≤
        phaseIntegral T - phaseIntegral (S ∪ T) := by linarith
    have hsum_eq :
        (∑ q ∈ (S ∪ T) \ T, (2 : ℝ) / ((q + 1) * (q + 3))) =
          ∑ q ∈ S \ T, (2 : ℝ) / ((q + 1) * (q + 3)) := by
      refine Finset.sum_congr ?_ (fun q _ => rfl)
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨by
          rcases (Finset.mem_union.mp hq'.1) with hqS | hqT
          · exact hqS
          · exact False.elim (hq'.2 hqT), hq'.2⟩
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left T hq'.1, hq'.2⟩
    exact hdiff.trans (hsharp.trans (by
      rw [hsum_eq]
      exact sum_kernel_le_sum_symmDiff_left S T))

/--
Assumption-free universal finite modulus of continuity.

The phase integral is 1-Lipschitz for the coarse weighted symmetric-difference
distance with kernel `1 / (q + 1)`.
-/
theorem phaseIntegral_lipschitz_loose (S T : Finset ℕ) :
    |phaseIntegral S - phaseIntegral T| ≤ looseSymmDiffDist S T := by
  rw [abs_sub_le_iff]
  constructor
  · have hS_union : S ⊆ S ∪ T := Finset.subset_union_left
    have hloose :
        phaseIntegral S - phaseIntegral (S ∪ T) ≤
          ∑ q ∈ (S ∪ T) \ S, (1 : ℝ) / (q + 1) :=
      loose_error_bound hS_union
    have hTu : phaseIntegral (S ∪ T) ≤ phaseIntegral T :=
      phaseIntegral_antitone Finset.subset_union_right
    have hdiff : phaseIntegral S - phaseIntegral T ≤
        phaseIntegral S - phaseIntegral (S ∪ T) := by linarith
    have hsum_eq :
        (∑ q ∈ (S ∪ T) \ S, (1 : ℝ) / (q + 1)) =
          ∑ q ∈ T \ S, (1 : ℝ) / (q + 1) := by
      refine Finset.sum_congr ?_ (fun q _ => rfl)
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨by
          rcases (Finset.mem_union.mp hq'.1) with hqS | hqT
          · exact False.elim (hq'.2 hqS)
          · exact hqT, hq'.2⟩
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right S hq'.1, hq'.2⟩
    exact hdiff.trans (hloose.trans (by
      rw [hsum_eq]
      exact sum_loose_kernel_le_sum_symmDiff_right S T))
  · have hT_union : T ⊆ S ∪ T := Finset.subset_union_right
    have hloose :
        phaseIntegral T - phaseIntegral (S ∪ T) ≤
          ∑ q ∈ (S ∪ T) \ T, (1 : ℝ) / (q + 1) :=
      loose_error_bound hT_union
    have hSu : phaseIntegral (S ∪ T) ≤ phaseIntegral S :=
      phaseIntegral_antitone Finset.subset_union_left
    have hdiff : phaseIntegral T - phaseIntegral S ≤
        phaseIntegral T - phaseIntegral (S ∪ T) := by linarith
    have hsum_eq :
        (∑ q ∈ (S ∪ T) \ T, (1 : ℝ) / (q + 1)) =
          ∑ q ∈ S \ T, (1 : ℝ) / (q + 1) := by
      refine Finset.sum_congr ?_ (fun q _ => rfl)
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨by
          rcases (Finset.mem_union.mp hq'.1) with hqS | hqT
          · exact hqS
          · exact False.elim (hq'.2 hqT), hq'.2⟩
      · intro hq
        have hq' := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left T hq'.1, hq'.2⟩
    exact hdiff.trans (hloose.trans (by
      rw [hsum_eq]
      exact sum_loose_kernel_le_sum_symmDiff_left S T))

/-- Replacing every exponent by a larger one increases every factor on `[0,1]`. -/
theorem one_sub_pow_le_one_sub_pow_of_le {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) {m n : ℕ} (hmn : m ≤ n) :
    1 - u ^ m ≤ 1 - u ^ n := by
  have hp : u ^ n ≤ u ^ m := pow_le_pow_of_le_one hu.1 hu.2 hmn
  linarith

/-- If all exponents in `S` are at least `m`, the product dominates `(1-u^m)^|S|`. -/
theorem phaseProduct_ge_card_power_of_forall_le {S : Finset ℕ} {m : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hmin : ∀ n ∈ S, m ≤ n) :
    (1 - u ^ m) ^ S.card ≤ phaseProduct S u := by
  unfold phaseProduct
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod
    (fun n hn => one_sub_pow_nonneg_of_mem_Icc hu m)
    (fun n hn => one_sub_pow_le_one_sub_pow_of_le hu (hmin n hn))

/-- First-element upper bound: membership of `m` forces `F[S] ≤ F[{m}]`. -/
theorem phaseIntegral_le_singleton_of_mem {S : Finset ℕ} {m : ℕ} (hm : m ∈ S) :
    phaseIntegral S ≤ phaseIntegral ({m} : Finset ℕ) := by
  exact phaseIntegral_antitone (by
    intro n hn
    have hn' : n = m := by simpa using hn
    simpa [hn'] using hm)

/--
First-element/cardinality lower bound in integral form.

If every exponent of `S` is at least `m`, then `F[S]` is bounded below by the
integral of the uniform product `(1-u^m)^|S|`.
-/
theorem card_power_integral_le_phaseIntegral {S : Finset ℕ} {m : ℕ}
    (hmin : ∀ n ∈ S, m ≤ n) :
    (∫ u in (0 : ℝ)..1, (1 - u ^ m) ^ S.card) ≤ phaseIntegral S := by
  unfold phaseIntegral
  exact intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun u => (1 - u ^ m) ^ S.card)
    (g := fun u => phaseProduct S u)
    (by norm_num)
    (((continuous_const.sub (continuous_id.pow m)).pow S.card).intervalIntegrable 0 1)
    (intervalIntegrable_phaseProduct S)
    (fun _u hu => phaseProduct_ge_card_power_of_forall_le hu hmin)

/-- Combined first-element bounds for a finite set with chosen minimum witness. -/
theorem first_element_bounds {S : Finset ℕ} {m : ℕ}
    (hm : m ∈ S) (hmin : ∀ n ∈ S, m ≤ n) :
    (∫ u in (0 : ℝ)..1, (1 - u ^ m) ^ S.card) ≤ phaseIntegral S ∧
      phaseIntegral S ≤ phaseIntegral ({m} : Finset ℕ) :=
  ⟨card_power_integral_le_phaseIntegral hmin, phaseIntegral_le_singleton_of_mem hm⟩

end ProductInvariants
