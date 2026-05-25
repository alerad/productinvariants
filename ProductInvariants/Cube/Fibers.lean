import ProductInvariants.Cube.SignedCube

namespace ProductInvariants

def subsetSumFiber (S : Finset ℕ) (m : ℕ) : Finset (Finset ℕ) :=
  S.powerset.filter (fun A => subsetSum A = m)

def signedFiberCoeff (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ A ∈ subsetSumFiber S m, subsetSign A

theorem mem_subsetSumFiber {S A : Finset ℕ} {m : ℕ} :
    A ∈ subsetSumFiber S m ↔ A ⊆ S ∧ subsetSum A = m := by
  simp [subsetSumFiber]

theorem signedFiberCoeff_def (S : Finset ℕ) (m : ℕ) :
    signedFiberCoeff S m =
      ∑ A ∈ S.powerset.filter (fun A => subsetSum A = m), subsetSign A := rfl

theorem signedFiberCoeff_eq_zero_of_gt {S : Finset ℕ} {m : ℕ}
    (hm : subsetSum S < m) :
    signedFiberCoeff S m = 0 := by
  classical
  unfold signedFiberCoeff subsetSumFiber
  rw [Finset.sum_eq_zero]
  intro A hA
  exfalso
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  have hAS : A ⊆ S := hA.1
  have hsum_le : subsetSum A ≤ subsetSum S := by
    unfold subsetSum
    exact Finset.sum_le_sum_of_subset_of_nonneg hAS
      (by intro x _hxS _hxA; exact Nat.zero_le x)
  omega

/-- The signed fiber coefficients are exactly the coefficients of the
subset-sum shadow polynomial. -/
theorem phaseProduct_eq_signedFiberCoeff_sum (S : Finset ℕ) (u : ℝ) :
    phaseProduct S u =
      ∑ m ∈ S.powerset.image subsetSum,
        signedFiberCoeff S m * u ^ m := by
  classical
  rw [phaseProduct_powersetExpansion]
  unfold signedFiberCoeff subsetSumFiber subsetSign
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := S.powerset)
    (t := S.powerset.image subsetSum)
    (g := subsetSum)
    (f := fun A => (-1 : ℝ) ^ A.card * u ^ subsetSum A)
    (by intro A hA; exact Finset.mem_image_of_mem subsetSum hA)]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  have hAm : subsetSum A = m := by
    simpa using (Finset.mem_filter.mp hA).2
  rw [hAm]

/--
The phase integral is the weighted signed-fiber spectrum:
`F_S = Σ_m c_m(S)/(1+m)`.

This is the precise statement that the scalar invariant only sees the signed
net mass left after the subset-sum observer collapses cube vertices into
fibers.
-/
theorem phaseIntegral_eq_signedFiberCoeff_sum (S : Finset ℕ) :
    phaseIntegral S =
      ∑ m ∈ S.powerset.image subsetSum,
        signedFiberCoeff S m / (1 + (m : ℝ)) := by
  classical
  unfold phaseIntegral
  have h_fun :
      (fun u : ℝ => phaseProduct S u) =
        fun u => ∑ m ∈ S.powerset.image subsetSum,
          signedFiberCoeff S m * u ^ m := by
    funext u
    exact phaseProduct_eq_signedFiberCoeff_sum S u
  rw [h_fun]
  rw [intervalIntegral.integral_finset_sum
    (s := S.powerset.image subsetSum)
    (fun _ _ => (Continuous.intervalIntegrable (by continuity) 0 1))]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- In the fiber `m = 5` for `{2, 3, 5}`, `{5}` and `{2, 3}` cancel. -/
theorem signedFiberCoeff_five_cancel :
    signedFiberCoeff ({2, 3, 5} : Finset ℕ) 5 = 0 := by
  classical
  have hfiber :
      subsetSumFiber ({2, 3, 5} : Finset ℕ) 5 =
        ({({5} : Finset ℕ), ({2, 3} : Finset ℕ)} :
          Finset (Finset ℕ)) := by
    decide
  unfold signedFiberCoeff
  rw [hfiber]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    norm_num [subsetSign]
  · decide

end ProductInvariants
