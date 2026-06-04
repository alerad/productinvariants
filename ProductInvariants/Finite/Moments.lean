import ProductInvariants.Cube.Fibers

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

/--
Moment version of the signed fiber expansion.

The `k`th moment only sees the signed subset-sum fiber coefficient at each
exponent, weighted by the shifted monomial integral.
-/
theorem phaseMoment_eq_signedFiberCoeff_sum (S : Finset ℕ) (k : ℕ) :
    phaseMoment S k =
      ∑ m ∈ S.powerset.image subsetSum,
        signedFiberCoeff S m / (1 + (((m + k : ℕ) : ℝ))) := by
  classical
  unfold phaseMoment
  have h_fun :
      (fun u : ℝ => phaseProduct S u * u ^ k) =
        fun u =>
          (∑ m ∈ S.powerset.image subsetSum,
            signedFiberCoeff S m * u ^ m) * u ^ k := by
    funext u
    rw [phaseProduct_eq_signedFiberCoeff_sum S u]
  rw [h_fun]
  have h_expand :
      (fun u : ℝ =>
          (∑ m ∈ S.powerset.image subsetSum,
            signedFiberCoeff S m * u ^ m) * u ^ k) =
        fun u =>
          ∑ m ∈ S.powerset.image subsetSum,
            signedFiberCoeff S m * u ^ m * u ^ k := by
    funext u
    rw [Finset.sum_mul]
  rw [h_expand]
  rw [intervalIntegral.integral_finset_sum
    (s := S.powerset.image subsetSum)]
  · refine Finset.sum_congr rfl ?_
    intro m _hm
    have h_term :
        (fun u : ℝ => signedFiberCoeff S m * u ^ m * u ^ k) =
          fun u : ℝ => signedFiberCoeff S m * u ^ (m + k) := by
      funext u
      rw [pow_add]
      ring
    rw [h_term, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  · intro m _hm
    exact ((continuous_const.mul (continuous_id.pow m)).mul
      (continuous_id.pow k)).intervalIntegrable 0 1

/-!
## Finite alternating moment transform

This is the finite Lean bridge to the Dirichlet-eta kernel.  The finite
alternating geometric kernel tends pointwise on `[0, 1)` to `1 / (1 + u)`,
so the limiting transform is the product-twisted eta integral
`∫_0^1 P[S](u) / (1 + u) du`.
-/

/-- Finite alternating transform of the phase moments. -/
noncomputable def alternatingPhaseMomentTransform
    (S : Finset ℕ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * phaseMoment S k

/--
Finite Dirichlet-eta kernel identity.

This rewrites the finite alternating transform of the phase moments as a
single integral against the finite alternating geometric kernel.
-/
theorem alternatingPhaseMomentTransform_eq_integral
    (S : Finset ℕ) (K : ℕ) :
    alternatingPhaseMomentTransform S K =
      ∫ u in (0 : ℝ)..1,
        phaseProduct S u *
          (∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * u ^ k) := by
  unfold alternatingPhaseMomentTransform phaseMoment
  calc
    (∑ k ∈ Finset.range K,
        (-1 : ℝ) ^ k * ∫ u in (0 : ℝ)..1, phaseProduct S u * u ^ k)
        =
      ∑ k ∈ Finset.range K,
        ∫ u in (0 : ℝ)..1, (-1 : ℝ) ^ k * (phaseProduct S u * u ^ k) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          rw [intervalIntegral.integral_const_mul]
    _ =
      ∫ u in (0 : ℝ)..1,
        ∑ k ∈ Finset.range K,
          (-1 : ℝ) ^ k * (phaseProduct S u * u ^ k) := by
          rw [intervalIntegral.integral_finset_sum]
          intro k _hk
          exact (continuous_const.mul
            ((continuous_phaseProduct S).mul (continuous_id.pow k))).intervalIntegrable 0 1
    _ =
      ∫ u in (0 : ℝ)..1,
        phaseProduct S u *
          (∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * u ^ k) := by
          apply intervalIntegral.integral_congr
          intro u _hu
          dsimp
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k _hk
          ring

end ProductInvariants
