import Mathlib.Data.PNat.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Defs
import ProductInvariants.Finite.ChebyshevIntegral

open MeasureTheory Set
open scoped symmDiff

namespace ProductInvariants

/-- Product profile for finite sets of positive exponents. -/
noncomputable def productProfileP (S : Finset ℕ+) (u : ℝ) : ℝ :=
  ∏ n ∈ S, (1 - u ^ (n : ℕ))

/-- Product-integral signature for finite sets of positive exponents. -/
noncomputable def phaseIntegralP (S : Finset ℕ+) : ℝ :=
  ∫ u in (0 : ℝ)..1, productProfileP S u

/-- Logarithmic phase energy attached to a positive-exponent set. -/
noncomputable def phaseEnergy (S : Finset ℕ+) : ℝ :=
  -Real.log (phaseIntegralP S)

/-- Symmetric-difference phase distance. -/
noncomputable def phaseDist (A B : Finset ℕ+) : ℝ :=
  phaseEnergy (A ∆ B)

@[simp]
theorem productProfileP_empty (u : ℝ) :
    productProfileP ∅ u = 1 := by
  simp [productProfileP]

@[simp]
theorem phaseIntegralP_empty :
    phaseIntegralP ∅ = 1 := by
  simp [phaseIntegralP]

@[simp]
theorem phaseEnergy_empty :
    phaseEnergy ∅ = 0 := by
  simp [phaseEnergy]

theorem productProfileP_zero (S : Finset ℕ+) :
    productProfileP S 0 = 1 := by
  unfold productProfileP
  apply Finset.prod_eq_one
  intro n _hn
  simp [zero_pow n.pos.ne']

theorem productProfileP_one_of_nonempty
    (S : Finset ℕ+) (hS : S.Nonempty) :
    productProfileP S 1 = 0 := by
  unfold productProfileP
  rcases hS with ⟨n, hn⟩
  exact Finset.prod_eq_zero hn (by simp)

theorem productProfileP_nonneg_on_Icc (S : Finset ℕ+) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ productProfileP S u := by
  unfold productProfileP
  apply Finset.prod_nonneg
  intro n _hn
  exact sub_nonneg.mpr (pow_le_one₀ hu.1 hu.2)

theorem productProfileP_le_one_on_Icc (S : Finset ℕ+) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    productProfileP S u ≤ 1 := by
  unfold productProfileP
  have h : ∏ n ∈ S, (1 - u ^ (n : ℕ)) ≤ ∏ n ∈ S, (1 : ℝ) := by
    apply Finset.prod_le_prod
    · intro n _hn
      exact sub_nonneg.mpr (pow_le_one₀ hu.1 hu.2)
    · intro n _hn
      exact sub_le_self 1 (pow_nonneg hu.1 (n : ℕ))
  simpa using h

/-- Adding positive exponents lowers the profile pointwise on `[0,1]`. -/
theorem productProfileP_antitone {S T : Finset ℕ+} (hST : S ⊆ T)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    productProfileP T u ≤ productProfileP S u := by
  unfold productProfileP
  exact Finset.prod_le_prod_of_subset_of_le_one hST
    (fun n _hn => sub_nonneg.mpr (pow_le_one₀ hu.1 hu.2))
    (fun n _hn _hns => sub_le_self 1 (pow_nonneg hu.1 (n : ℕ)))

/-- Every finite positive-exponent product profile is antitone on `[0,1]`. -/
theorem productProfileP_antitoneOn (S : Finset ℕ+) :
    AntitoneOn (productProfileP S) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  unfold productProfileP
  apply Finset.prod_le_prod
  · intro n _hn
    exact sub_nonneg.mpr (pow_le_one₀ hy.1 hy.2)
  · intro n _hn
    exact sub_le_sub_left (pow_le_pow_left₀ hx.1 hxy (n : ℕ)) 1

theorem continuous_productProfileP (S : Finset ℕ+) :
    Continuous fun u : ℝ => productProfileP S u := by
  unfold productProfileP
  exact continuous_finset_prod S
    (fun n _hn => continuous_const.sub (continuous_id.pow (n : ℕ)))

theorem intervalIntegrable_productProfileP (S : Finset ℕ+) :
    IntervalIntegrable (productProfileP S) volume 0 1 :=
  (continuous_productProfileP S).intervalIntegrable 0 1

theorem intervalIntegrable_productProfileP_mul (A B : Finset ℕ+) :
    IntervalIntegrable (fun u => productProfileP A u * productProfileP B u) volume 0 1 :=
  ((continuous_productProfileP A).mul (continuous_productProfileP B)).intervalIntegrable 0 1

theorem productProfileP_union_eq_mul_sdiff (A B : Finset ℕ+) (u : ℝ) :
    productProfileP (A ∪ B) u = productProfileP A u * productProfileP (B \ A) u := by
  classical
  unfold productProfileP
  have hdisj : Disjoint A (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hxA hxBA
    exact (Finset.mem_sdiff.mp hxBA).2 hxA
  have hunion : A ∪ (B \ A) = A ∪ B := by
    ext x
    by_cases hxA : x ∈ A <;> simp [hxA]
  rw [← hunion, Finset.prod_union hdisj]

/-- On `[0,1]`, the product of two profiles is bounded by the profile of their union. -/
theorem productProfileP_mul_le_union (A B : Finset ℕ+) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    productProfileP A u * productProfileP B u ≤ productProfileP (A ∪ B) u := by
  classical
  have hA0 : 0 ≤ productProfileP A u := productProfileP_nonneg_on_Icc A hu
  have hB_le : productProfileP B u ≤ productProfileP (B \ A) u := by
    exact productProfileP_antitone (fun x hx => (Finset.mem_sdiff.mp hx).1) hu
  calc
    productProfileP A u * productProfileP B u
        ≤ productProfileP A u * productProfileP (B \ A) u :=
          mul_le_mul_of_nonneg_left hB_le hA0
    _ = productProfileP (A ∪ B) u := (productProfileP_union_eq_mul_sdiff A B u).symm

theorem phaseIntegralP_pos (S : Finset ℕ+) :
    0 < phaseIntegralP S := by
  unfold phaseIntegralP
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
  · exact (continuous_productProfileP S).continuousOn
  · intro x hx
    exact productProfileP_nonneg_on_Icc S ⟨le_of_lt hx.1, hx.2⟩
  · exact ⟨0, by simp, by simp [productProfileP_zero S]⟩

theorem phaseIntegralP_le_one (S : Finset ℕ+) :
    phaseIntegralP S ≤ 1 := by
  unfold phaseIntegralP
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_productProfileP S) hconst
    (fun x hx => productProfileP_le_one_on_Icc S hx)
  simpa using hmono

theorem phaseIntegralP_lt_one_of_nonempty
    (S : Finset ℕ+) (hS : S.Nonempty) :
    phaseIntegralP S < 1 := by
  unfold phaseIntegralP
  have hconst_cont : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) 1) :=
    continuous_const.continuousOn
  have hprod_cont : ContinuousOn (productProfileP S) (Icc (0 : ℝ) 1) :=
    (continuous_productProfileP S).continuousOn
  have hle : ∀ x ∈ Ioc (0 : ℝ) 1, productProfileP S x ≤ 1 := by
    intro x hx
    exact productProfileP_le_one_on_Icc S ⟨le_of_lt hx.1, hx.2⟩
  have hlt : ∃ c ∈ Icc (0 : ℝ) 1, productProfileP S c < (fun _ : ℝ => (1 : ℝ)) c := by
    exact ⟨1, by simp, by simp [productProfileP_one_of_nonempty S hS]⟩
  have hstrict :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by norm_num : (0 : ℝ) < 1) hprod_cont hconst_cont hle hlt
  simpa [intervalIntegral.integral_const] using hstrict

theorem phaseIntegralP_nonempty_lt_one_iff (S : Finset ℕ+) :
    phaseIntegralP S < 1 ↔ S.Nonempty := by
  constructor
  · intro h
    by_contra hne
    have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hEmpty] at h
  · exact phaseIntegralP_lt_one_of_nonempty S

theorem phaseIntegralP_mono_of_subset {A B : Finset ℕ+} (hAB : A ⊆ B) :
    phaseIntegralP B ≤ phaseIntegralP A := by
  unfold phaseIntegralP
  exact intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_productProfileP B)
    (intervalIntegrable_productProfileP A)
    (fun x hx => productProfileP_antitone hAB hx)

/-- Chebyshev supermultiplicativity for finite positive-exponent product integrals. -/
theorem productInvariant_supermultiplicative (A B : Finset ℕ+) :
    phaseIntegralP A * phaseIntegralP B ≤ phaseIntegralP (A ∪ B) := by
  unfold phaseIntegralP
  have hcheb :
      (∫ x in (0 : ℝ)..1, productProfileP A x) *
          (∫ y in (0 : ℝ)..1, productProfileP B y) ≤
        ∫ u in (0 : ℝ)..1, productProfileP A u * productProfileP B u :=
    chebyshev_integral_antitone
      (productProfileP_antitoneOn A)
      (productProfileP_antitoneOn B)
      (intervalIntegrable_productProfileP A)
      (intervalIntegrable_productProfileP B)
      (intervalIntegrable_productProfileP_mul A B)
  have hpoint :
      (∫ u in (0 : ℝ)..1, productProfileP A u * productProfileP B u) ≤
        ∫ u in (0 : ℝ)..1, productProfileP (A ∪ B) u :=
    intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (intervalIntegrable_productProfileP_mul A B)
      (intervalIntegrable_productProfileP (A ∪ B))
      (fun x hx => productProfileP_mul_le_union A B hx)
  exact hcheb.trans hpoint

theorem phaseEnergy_nonneg (S : Finset ℕ+) :
    0 ≤ phaseEnergy S := by
  unfold phaseEnergy
  have hpos := phaseIntegralP_pos S
  have hle := phaseIntegralP_le_one S
  have hlog : Real.log (phaseIntegralP S) ≤ Real.log 1 :=
    Real.log_le_log hpos hle
  have hlog0 : Real.log (phaseIntegralP S) ≤ 0 := by
    simpa using hlog
  linarith

theorem phaseEnergy_eq_zero_iff_empty (S : Finset ℕ+) :
    phaseEnergy S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    by_contra hne
    have hnon : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have hlt := phaseIntegralP_lt_one_of_nonempty S hnon
    have hpos := phaseIntegralP_pos S
    have hlogneg : Real.log (phaseIntegralP S) < 0 := by
      simpa using Real.log_neg hpos hlt
    unfold phaseEnergy at h
    linarith
  · intro h
    simp [h]

theorem phaseEnergy_mono_of_subset {A B : Finset ℕ+} (hAB : A ⊆ B) :
    phaseEnergy A ≤ phaseEnergy B := by
  unfold phaseEnergy
  have hposA := phaseIntegralP_pos A
  have hmono := phaseIntegralP_mono_of_subset hAB
  have hlog : Real.log (phaseIntegralP B) ≤ Real.log (phaseIntegralP A) :=
    Real.log_le_log (phaseIntegralP_pos B) hmono
  linarith

/-- Log phase energy is subadditive under union. -/
theorem phaseEnergy_subadditive (A B : Finset ℕ+) :
    phaseEnergy (A ∪ B) ≤ phaseEnergy A + phaseEnergy B := by
  unfold phaseEnergy
  have hA := phaseIntegralP_pos A
  have hB := phaseIntegralP_pos B
  have hU := phaseIntegralP_pos (A ∪ B)
  have hmul_pos : 0 < phaseIntegralP A * phaseIntegralP B := mul_pos hA hB
  have hsuper := productInvariant_supermultiplicative A B
  have hlog : Real.log (phaseIntegralP A * phaseIntegralP B) ≤
      Real.log (phaseIntegralP (A ∪ B)) :=
    Real.log_le_log hmul_pos hsuper
  rw [Real.log_mul hA.ne' hB.ne'] at hlog
  linarith

theorem symmDiff_subset_union_symmDiff
    (A B C : Finset ℕ+) :
    A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C) := by
  classical
  intro x hx
  rw [Finset.mem_union]
  rw [Finset.mem_symmDiff] at hx ⊢
  rw [Finset.mem_symmDiff]
  tauto

@[simp]
theorem phaseDist_self (A : Finset ℕ+) :
    phaseDist A A = 0 := by
  simp [phaseDist]

theorem phaseDist_comm (A B : Finset ℕ+) :
    phaseDist A B = phaseDist B A := by
  simp [phaseDist, symmDiff_comm]

theorem phaseDist_nonneg (A B : Finset ℕ+) :
    0 ≤ phaseDist A B :=
  phaseEnergy_nonneg (A ∆ B)

theorem phaseDist_eq_zero_iff (A B : Finset ℕ+) :
    phaseDist A B = 0 ↔ A = B := by
  rw [phaseDist, phaseEnergy_eq_zero_iff_empty, Finset.symmDiff_eq_empty]

/-- Triangle inequality for symmetric-difference phase distance. -/
theorem phaseDist_triangle (A B C : Finset ℕ+) :
    phaseDist A C ≤ phaseDist A B + phaseDist B C := by
  unfold phaseDist
  have hsubset := symmDiff_subset_union_symmDiff A B C
  exact (phaseEnergy_mono_of_subset hsubset).trans
    (phaseEnergy_subadditive (A ∆ B) (B ∆ C))

/-- The product-integral phase distance packages as a genuine metric space.

This is deliberately a named metric structure rather than a global instance, so
it does not overwrite Mathlib's existing topology on `Finset ℕ+`. -/
@[reducible]
noncomputable def phaseMetricSpace : MetricSpace (Finset ℕ+) where
  dist := phaseDist
  dist_self := phaseDist_self
  dist_comm := phaseDist_comm
  dist_triangle := phaseDist_triangle
  eq_of_dist_eq_zero := by
    intro A B h
    exact (phaseDist_eq_zero_iff A B).mp h

@[simp]
theorem phaseMetricSpace_dist_eq (A B : Finset ℕ+) :
    @dist (Finset ℕ+) phaseMetricSpace.toDist A B = phaseDist A B := rfl

theorem symmDiff_subset_union (A B : Finset ℕ+) :
    A ∆ B ⊆ A ∪ B :=
  Finset.symmDiff_subset_union

/-- The distance between two sets is bounded by the energy of their union. -/
theorem phaseDist_le_phaseEnergy_union (A B : Finset ℕ+) :
    phaseDist A B ≤ phaseEnergy (A ∪ B) := by
  exact phaseEnergy_mono_of_subset (symmDiff_subset_union A B)

theorem symmDiff_subset_of_subset {A B U : Finset ℕ+}
    (hA : A ⊆ U) (hB : B ⊆ U) :
    A ∆ B ⊆ U := by
  intro x hx
  rw [Finset.mem_symmDiff] at hx
  rcases hx with ⟨hxA, _⟩ | ⟨hxB, _⟩
  · exact hA hxA
  · exact hB hxB

/-- Finite-universe diameter bound: all subsets of `U` have diameter at most
`χ(U) = -log F_U`. -/
theorem phaseDist_le_phaseEnergy_of_subset {A B U : Finset ℕ+}
    (hA : A ⊆ U) (hB : B ⊆ U) :
    phaseDist A B ≤ phaseEnergy U := by
  exact phaseEnergy_mono_of_subset (symmDiff_subset_of_subset hA hB)

/-- The bounded finite phase universe over a fixed support `U`. -/
def FinsetsIn (U : Finset ℕ+) :=
  { S : Finset ℕ+ // S ⊆ U }

/-- All points of the finite phase universe over `U` are mutually within
`χ(U)`. -/
theorem phaseDiameter_le (U : Finset ℕ+) (A B : FinsetsIn U) :
    phaseDist A.1 B.1 ≤ phaseEnergy U :=
  phaseDist_le_phaseEnergy_of_subset A.property B.property

end ProductInvariants
