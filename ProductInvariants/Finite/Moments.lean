import ProductInvariants.Finite.PowersetExpansion

open MeasureTheory intervalIntegral

namespace ProductInvariants

/-!
# Moment expansion

The scalar invariant `phaseIntegral S` is the zeroth member of a monomial
moment family.  This is the finite product analogue of expanding a q-product
and integrating termwise.
-/

/-- The `k`th moment of the product profile attached to `S`. -/
noncomputable def phaseMoment (S : Finset ℕ) (k : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, phaseProduct S u * u ^ k

/-- The phase integral is the zeroth product-profile moment. -/
theorem phaseMoment_zero (S : Finset ℕ) :
    phaseMoment S 0 = phaseIntegral S := by
  unfold phaseMoment phaseIntegral
  apply intervalIntegral.integral_congr
  intro u _hu
  simp

theorem interval_integral_signed_pow_shift (A : Finset ℕ) (k : ℕ) :
    (∫ u in (0 : ℝ)..1, subsetSign A * u ^ subsetSum A * u ^ k) =
      subsetSign A / (1 + ((subsetSum A + k : ℕ) : ℝ)) := by
  have hpow :
      (fun u : ℝ => subsetSign A * u ^ subsetSum A * u ^ k) =
        fun u : ℝ => subsetSign A * u ^ (subsetSum A + k) := by
    funext u
    rw [pow_add]
    ring
  rw [hpow, intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/--
Moment version of the signed subset-sum expansion.

For `k = 0` this recovers `phaseIntegral_eq_sum_powerset`.
-/
theorem phaseMoment_eq_sum_powerset (S : Finset ℕ) (k : ℕ) :
    phaseMoment S k =
      ∑ A ∈ S.powerset,
        subsetSign A / (1 + ((subsetSum A + k : ℕ) : ℝ)) := by
  unfold phaseMoment
  rw [intervalIntegral.integral_congr]
  · rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro A _hA
      rw [interval_integral_signed_pow_shift]
    · intro A _hA
      exact ((continuous_const.mul (continuous_id.pow (subsetSum A))).mul
        (continuous_id.pow k)).intervalIntegrable 0 1
  · intro u _hu
    change phaseProduct S u * u ^ k =
      ∑ A ∈ S.powerset, subsetSign A * u ^ subsetSum A * u ^ k
    rw [phaseProduct_powersetExpansion]
    rw [Finset.sum_mul]

end ProductInvariants
