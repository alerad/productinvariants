import Mathlib

namespace ProductInvariants

/-- The finite phase product attached to a set of exponents. -/
def phaseProduct (S : Finset ℕ) (u : ℝ) : ℝ :=
  S.prod (fun n => 1 - u ^ n)

notation "P[" S "]" => phaseProduct S

@[simp]
theorem phaseProduct_empty (u : ℝ) :
    phaseProduct ∅ u = 1 := by
  simp [phaseProduct]

theorem one_sub_pow_nonneg_of_mem_Icc {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    0 ≤ 1 - u ^ n := by
  have hp1 : u ^ n ≤ 1 := pow_le_one₀ hu.1 hu.2
  linarith

theorem one_sub_pow_le_one_of_mem_Icc {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    1 - u ^ n ≤ 1 := by
  have hp0 : 0 ≤ u ^ n := pow_nonneg hu.1 n
  linarith

theorem phaseProduct_nonneg_on_Icc (S : Finset ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ phaseProduct S u := by
  unfold phaseProduct
  exact Finset.prod_nonneg
    (fun n _hn => one_sub_pow_nonneg_of_mem_Icc hu n)

theorem phaseProduct_le_one_on_Icc (S : Finset ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    phaseProduct S u ≤ 1 := by
  unfold phaseProduct
  have h : ∏ n ∈ S, (1 - u ^ n) ≤ ∏ n ∈ S, (1 : ℝ) := by
    exact Finset.prod_le_prod (s := S)
      (fun n _hn => one_sub_pow_nonneg_of_mem_Icc hu n)
      (fun n _hn => one_sub_pow_le_one_of_mem_Icc hu n)
  simpa using h

theorem phaseProduct_antitone {S T : Finset ℕ} (hST : S ⊆ T)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    phaseProduct T u ≤ phaseProduct S u := by
  unfold phaseProduct
  exact Finset.prod_le_prod_of_subset_of_le_one hST
    (fun n _hn => one_sub_pow_nonneg_of_mem_Icc hu n)
    (fun n _hn _hns => one_sub_pow_le_one_of_mem_Icc hu n)

theorem continuous_phaseProduct (S : Finset ℕ) :
    Continuous fun u : ℝ => phaseProduct S u := by
  unfold phaseProduct
  exact continuous_finset_prod S
    (fun n _hn => continuous_const.sub (continuous_id.pow n))

end ProductInvariants
