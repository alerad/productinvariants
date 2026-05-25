import ProductInvariants.Finite.Integral

open MeasureTheory intervalIntegral

namespace ProductInvariants

theorem phaseIntegral_antitone {S T : Finset ℕ} (hST : S ⊆ T) :
    phaseIntegral T ≤ phaseIntegral S := by
  unfold phaseIntegral
  exact intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun u => phaseProduct T u) (g := fun u => phaseProduct S u)
    (by norm_num)
    (intervalIntegrable_phaseProduct T)
    (intervalIntegrable_phaseProduct S)
    (fun _u hu => phaseProduct_antitone hST hu)

theorem phaseIntegral_unit_interval_bounds (S : Finset ℕ) :
    0 ≤ phaseIntegral S ∧ phaseIntegral S ≤ 1 :=
  ⟨phaseIntegral_nonneg S, phaseIntegral_le_one S⟩

theorem one_half_barrier {S : Finset ℕ} (h1 : 1 ∈ S) :
    phaseIntegral S ≤ (1 : ℝ) / 2 := by
  have hsub : {1} ⊆ S := by
    intro n hn
    have hn' : n = 1 := by
      simpa using hn
    simpa [hn'] using h1
  have hmono := phaseIntegral_antitone hsub
  have hsingle : phaseIntegral ({1} : Finset ℕ) = (1 : ℝ) / 2 := by
    rw [phaseIntegral_singleton 1]
    norm_num
  linarith

theorem phaseIntegral_pair_one_eq {m : ℕ} (hm : 1 < m) :
    phaseIntegral ({1, m} : Finset ℕ) =
      (1 : ℝ) / 2 - 1 / ((m + 1 : ℕ) : ℝ) + 1 / ((m + 2 : ℕ) : ℝ) := by
  unfold phaseIntegral phaseProduct
  calc
    (∫ u in (0 : ℝ)..1, ∏ n ∈ ({1, m} : Finset ℕ), (1 - u ^ n))
        = ∫ u in (0 : ℝ)..1, ((1 - u) * (1 - u ^ m)) := by
          apply intervalIntegral.integral_congr
          intro u _hu
          dsimp
          rw [Finset.prod_pair (a := 1) (b := m)
            (f := fun n : ℕ => 1 - u ^ n) (ne_of_lt hm)]
          simp
    _ = ∫ u in (0 : ℝ)..1, (1 - u - u ^ m + u ^ (m + 1)) := by
          apply intervalIntegral.integral_congr
          intro u _hu
          ring_nf
    _ = (1 : ℝ) / 2 - 1 / ((m + 1 : ℕ) : ℝ) + 1 / ((m + 2 : ℕ) : ℝ) := by
          have h_one : IntervalIntegrable (fun _u : ℝ => (1 : ℝ)) volume 0 1 :=
            (continuous_const).intervalIntegrable 0 1
          have h_id : IntervalIntegrable (fun u : ℝ => u) volume 0 1 :=
            (continuous_id).intervalIntegrable 0 1
          have h_pow_m : IntervalIntegrable (fun u : ℝ => u ^ m) volume 0 1 :=
            (continuous_id.pow m).intervalIntegrable 0 1
          have h_pow_succ : IntervalIntegrable (fun u : ℝ => u ^ (m + 1)) volume 0 1 :=
            (continuous_id.pow (m + 1)).intervalIntegrable 0 1
          have h_one_sub_id :
              IntervalIntegrable (fun u : ℝ => (1 : ℝ) - u) volume 0 1 :=
            (continuous_const.sub continuous_id).intervalIntegrable 0 1
          have h_left :
              IntervalIntegrable (fun u : ℝ => (1 : ℝ) - u - u ^ m) volume 0 1 :=
            ((continuous_const.sub continuous_id).sub
              (continuous_id.pow m)).intervalIntegrable 0 1
          rw [intervalIntegral.integral_add h_left h_pow_succ]
          rw [intervalIntegral.integral_sub h_one_sub_id h_pow_m]
          rw [intervalIntegral.integral_sub h_one h_id]
          simp [integral_pow]
          ring

theorem phaseIntegral_pair_one_lt_half {m : ℕ} (hm : 1 < m) :
    phaseIntegral ({1, m} : Finset ℕ) < (1 : ℝ) / 2 := by
  rw [phaseIntegral_pair_one_eq hm]
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hlt : ((m + 1 : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ) := by norm_num
  have hinvlt : (1 : ℝ) / ((m + 2 : ℕ) : ℝ) <
      1 / ((m + 1 : ℕ) : ℝ) :=
    one_div_lt_one_div_of_lt hpos hlt
  linarith

theorem one_half_barrier_strict_of_mem {S : Finset ℕ}
    (h1 : 1 ∈ S) {m : ℕ} (hm : m ∈ S) (hmgt : 1 < m) :
    phaseIntegral S < (1 : ℝ) / 2 := by
  have hsub : ({1, m} : Finset ℕ) ⊆ S := by
    intro n hn
    rw [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with hn | hn
    · simpa [hn] using h1
    · simpa [hn] using hm
  exact lt_of_le_of_lt (phaseIntegral_antitone hsub)
    (phaseIntegral_pair_one_lt_half hmgt)

end ProductInvariants
