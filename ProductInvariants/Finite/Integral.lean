import ProductInvariants.Finite.Product
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory intervalIntegral

namespace ProductInvariants

theorem continuous_phaseProduct (S : Finset ℕ) :
    Continuous fun u : ℝ => phaseProduct S u := by
  unfold phaseProduct
  exact continuous_finset_prod S
    (fun n _hn => continuous_const.sub (continuous_id.pow n))

/-- The finite phase integral attached to a set of exponents. -/
noncomputable def phaseIntegral (S : Finset ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, phaseProduct S u

notation "F[" S "]" => phaseIntegral S

theorem intervalIntegrable_phaseProduct (S : Finset ℕ) :
    IntervalIntegrable (fun u : ℝ => phaseProduct S u) volume (0 : ℝ) 1 :=
  (continuous_phaseProduct S).intervalIntegrable 0 1

@[simp]
theorem phaseIntegral_empty :
    phaseIntegral ∅ = 1 := by
  simp [phaseIntegral]

theorem phaseIntegral_singleton (n : ℕ) :
    phaseIntegral {n} = 1 - (1 : ℝ) / (n + 1) := by
  simp [phaseIntegral, phaseProduct, integral_pow]

theorem phaseIntegral_nonneg (S : Finset ℕ) :
    0 ≤ phaseIntegral S := by
  unfold phaseIntegral
  exact intervalIntegral.integral_nonneg (by norm_num)
    (fun _u hu => phaseProduct_nonneg_on_Icc S hu)

theorem phaseIntegral_pos_of_ne_zero {S : Finset ℕ}
    (hS : phaseIntegral S ≠ 0) :
    0 < phaseIntegral S :=
  lt_of_le_of_ne (phaseIntegral_nonneg S) hS.symm

theorem phaseIntegral_le_one (S : Finset ℕ) :
    phaseIntegral S ≤ 1 := by
  unfold phaseIntegral
  have h := intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun u => phaseProduct S u) (g := fun _ => (1 : ℝ))
    (by norm_num)
    (intervalIntegrable_phaseProduct S)
    (continuous_const.intervalIntegrable 0 1)
    (fun _u hu => phaseProduct_le_one_on_Icc S hu)
  simpa using h

end ProductInvariants
