import ProductInvariants.Finite.Integral

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace ProductInvariants

def subsetSum (A : Finset ℕ) : ℕ :=
  A.sum id

def subsetSign (A : Finset ℕ) : ℝ :=
  (-1 : ℝ) ^ A.card

theorem phaseProduct_powersetExpansion (S : Finset ℕ) (u : ℝ) :
    phaseProduct S u =
      ∑ A ∈ S.powerset, subsetSign A * u ^ subsetSum A := by
  classical
  refine Finset.induction_on S ?empty ?insert
  · simp [phaseProduct, subsetSign, subsetSum]
  · intro a S haS ih
    have ih' :
        ∏ n ∈ S, (1 - u ^ n) =
          ∑ A ∈ S.powerset, subsetSign A * u ^ subsetSum A := by
      simpa [phaseProduct] using ih
    have hmap :
        (∑ A ∈ S.powerset,
            subsetSign (insert a A) * u ^ subsetSum (insert a A)) =
          ∑ A ∈ S.powerset,
            (-(u ^ a)) * (subsetSign A * u ^ subsetSum A) := by
      refine Finset.sum_congr rfl ?_
      intro A hA
      have haA : a ∉ A := by
        rw [Finset.mem_powerset] at hA
        exact fun haA => haS (hA haA)
      simp [subsetSign, subsetSum, haA, pow_succ]
      ring
    calc
      phaseProduct (insert a S) u
          = (1 - u ^ a) * ∏ n ∈ S, (1 - u ^ n) := by
            rw [phaseProduct, Finset.prod_insert haS]
      _ = (1 - u ^ a) *
            ∑ A ∈ S.powerset, subsetSign A * u ^ subsetSum A := by
            rw [ih']
      _ = ∑ A ∈ (insert a S).powerset,
            subsetSign A * u ^ subsetSum A := by
            rw [Finset.sum_powerset_insert haS]
            rw [hmap]
            rw [← Finset.mul_sum]
            ring

theorem interval_integral_signed_pow (A : Finset ℕ) :
    (∫ u in (0 : ℝ)..1, subsetSign A * u ^ subsetSum A) =
      subsetSign A / (1 + (subsetSum A : ℝ)) := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem phaseIntegral_eq_sum_powerset (S : Finset ℕ) :
    phaseIntegral S =
      ∑ A ∈ S.powerset, subsetSign A / (1 + (subsetSum A : ℝ)) := by
  unfold phaseIntegral
  rw [intervalIntegral.integral_congr]
  · rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro A _hA
      rw [interval_integral_signed_pow]
    · intro A _hA
      exact (continuous_const.mul (continuous_id.pow (subsetSum A))).intervalIntegrable 0 1
  · intro u _hu
    exact phaseProduct_powersetExpansion S u

end ProductInvariants
