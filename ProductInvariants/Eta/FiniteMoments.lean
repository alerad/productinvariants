import ProductInvariants.Finite.Moments
import ProductInvariants.Cube.Fibers
import ProductInvariants.Directed.Predicate

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace ProductInvariants

/-!
# Finite eta-product moments

This file records the finite product-integral side of Glasser's eta-integral
identity.  It does not prove the classical hyperbolic closed form; rather, it
formalizes the exact finite approximation scheme obtained by truncating

`∏_{n ≥ 1} (1 - q^n)`.

Since `η(ix) = q^(1/24) ∏_{n ≥ 1} (1 - q^n)`, Glasser's integrand
`q^(y-1) η(ix)` equals

`q^(y - 23/24) ∏_{n ≥ 1} (1 - q^n)`.

Thus the integer moment `q^k` corresponds to the special parameters
`y = k + 23/24`.
-/

/-- The eta-product prefix `{1, 2, ..., N}`. -/
def etaPrefix (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n => 0 < n

@[simp]
theorem mem_etaPrefix {n N : ℕ} :
    n ∈ etaPrefix N ↔ 0 < n ∧ n ≤ N := by
  unfold etaPrefix
  simp [and_comm]

/--
Finite eta-product moment.

This is the finite version of Glasser's eta integral after removing the
`q^(1/24)` eta prefactor and specializing to integer moment parameter `k`.
-/
noncomputable def etaFiniteMoment (N k : ℕ) : ℝ :=
  phaseMoment (etaPrefix N) k

/--
Exact signed subset-sum expansion for finite eta-product moments.

This is the Lean-certified finite analogue of the product side of Glasser's
Eq. (4) at the integer-shift parameters `y = k + 23/24`.
-/
theorem etaFiniteMoment_eq_sum_powerset (N k : ℕ) :
    etaFiniteMoment N k =
      ∑ A ∈ (etaPrefix N).powerset,
        subsetSign A / (1 + (((subsetSum A + k : ℕ) : ℝ))) := by
  unfold etaFiniteMoment
  exact phaseMoment_eq_sum_powerset (etaPrefix N) k

/--
Fiber-observer version of the finite eta moment.

The subset-sum observer already contains all the finite eta-moment data: after
grouping subsets by equal sum, only the signed fiber coefficient remains.
-/
theorem etaFiniteMoment_eq_signedFiberCoeff_sum (N k : ℕ) :
    etaFiniteMoment N k =
      ∑ m ∈ (etaPrefix N).powerset.image subsetSum,
        signedFiberCoeff (etaPrefix N) m / (1 + (((m + k : ℕ) : ℝ))) := by
  classical
  unfold etaFiniteMoment phaseMoment
  have h_fun :
      (fun u : ℝ => phaseProduct (etaPrefix N) u * u ^ k) =
        fun u =>
          ∑ m ∈ (etaPrefix N).powerset.image subsetSum,
            signedFiberCoeff (etaPrefix N) m * u ^ (m + k) := by
    funext u
    rw [phaseProduct_eq_signedFiberCoeff_sum (etaPrefix N) u, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro m _hm
    rw [mul_assoc, pow_add]
  rw [h_fun, intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro m _hm
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  · intro m _hm
    exact (continuous_const.mul (continuous_id.pow (m + k))).intervalIntegrable 0 1

/--
Glasser-compatible finite left-hand side at integer-shift parameters.

For integer `k`, this corresponds to Glasser's parameter `y = k + 23/24`,
because `q^(y-1) η(ix) = q^k ∏_{n ≥ 1} (1 - q^n)`.
-/
noncomputable def glasserFiniteLHSIntegerShift (N k : ℕ) : ℝ :=
  etaFiniteMoment N k

theorem glasserFiniteLHSIntegerShift_eq_sum (N k : ℕ) :
    glasserFiniteLHSIntegerShift N k =
      ∑ A ∈ (etaPrefix N).powerset,
        subsetSign A / (1 + (((subsetSum A + k : ℕ) : ℝ))) := by
  unfold glasserFiniteLHSIntegerShift
  exact etaFiniteMoment_eq_sum_powerset N k

/-- Glasser's closed-form right side at the integer-shift parameters. -/
noncomputable def glasserRHSIntegerShift (k : ℕ) : ℝ :=
  let y : ℝ := (k : ℝ) + 23 / 24
  Real.pi * Real.sqrt (2 / y) *
    Real.sinh (Real.pi * Real.sqrt ((8 / 3) * y)) /
      Real.cosh (Real.pi * Real.sqrt (6 * y))

end ProductInvariants
