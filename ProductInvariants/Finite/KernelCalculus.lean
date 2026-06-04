import ProductInvariants.Finite.Moments
import ProductInvariants.Cube.Fibers

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace ProductInvariants

/-- Kernel attached to a common prefix `R`. -/
noncomputable def commonPrefixKernel (R : Finset ℕ) (q : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, phaseProduct R u * u ^ q

/-- The common-prefix error kernel is exactly a phase moment. -/
theorem commonPrefixKernel_eq_phaseMoment
    (R : Finset ℕ) (q : ℕ) :
    commonPrefixKernel R q = phaseMoment R q := rfl

/-- Multiplicative insertion of one exponent into a product state. -/
noncomputable def insertionOperator (q : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => f u * (1 - u ^ q)

/-- Inserting an exponent is multiplication by the insertion operator. -/
theorem phaseProduct_insert_of_not_mem
    {S : Finset ℕ} {q : ℕ} (hq : q ∉ S) :
    phaseProduct (insert q S) =
      insertionOperator q (phaseProduct S) := by
  funext u
  rw [phaseProduct, Finset.prod_insert hq]
  simp [insertionOperator, phaseProduct, mul_comm]

/--
Moment insertion law.

Adding exponent `q` applies the finite-difference shift
`M_k ↦ M_k - M_{k+q}` to the moment trajectory.
-/
theorem phaseMoment_insert_of_not_mem
    {S : Finset ℕ} {q k : ℕ} (hq : q ∉ S) :
    phaseMoment (insert q S) k =
      phaseMoment S k - phaseMoment S (k + q) := by
  calc
    phaseMoment (insert q S) k
        =
          ∫ u in (0 : ℝ)..1,
            phaseProduct S u * u ^ k - phaseProduct S u * u ^ (k + q) := by
          unfold phaseMoment
          apply intervalIntegral.integral_congr
          intro u _hu
          have hprod := congrFun (phaseProduct_insert_of_not_mem hq) u
          change phaseProduct (insert q S) u =
            phaseProduct S u * (1 - u ^ q) at hprod
          dsimp
          rw [hprod]
          rw [pow_add]
          ring
    _ = phaseMoment S k - phaseMoment S (k + q) := by
          unfold phaseMoment
          rw [intervalIntegral.integral_sub]
          · exact ((continuous_phaseProduct S).mul
              (continuous_id.pow k)).intervalIntegrable 0 1
          · exact ((continuous_phaseProduct S).mul
              (continuous_id.pow (k + q))).intervalIntegrable 0 1

/--
The common-prefix kernel is the exact one-exponent marginal decrement of the
finite product-integral.
-/
theorem phaseIntegral_insert_eq_sub_commonPrefixKernel
    {R : Finset ℕ} {q : ℕ} (hq : q ∉ R) :
    phaseIntegral (insert q R) =
      phaseIntegral R - commonPrefixKernel R q := by
  rw [commonPrefixKernel_eq_phaseMoment]
  simpa [phaseMoment_zero] using
    phaseMoment_insert_of_not_mem (S := R) (q := q) (k := 0) hq

/--
Equivalently, adjoining one exponent lowers the integral by exactly the kernel.
-/
theorem phaseIntegral_sub_insert_eq_commonPrefixKernel
    {R : Finset ℕ} {q : ℕ} (hq : q ∉ R) :
    phaseIntegral R - phaseIntegral (insert q R) =
      commonPrefixKernel R q := by
  rw [phaseIntegral_insert_eq_sub_commonPrefixKernel hq]
  ring

/--
The kernel is the integrated signed fiber spectrum with denominator shifted by
the forced observed weight `q`.
-/
theorem commonPrefixKernel_eq_signedFiberCoeff_sum
    (R : Finset ℕ) (q : ℕ) :
    commonPrefixKernel R q =
      ∑ m ∈ R.powerset.image subsetSum,
        signedFiberCoeff R m /
          (1 + (((m + q : ℕ) : ℝ))) := by
  rw [commonPrefixKernel_eq_phaseMoment]
  exact phaseMoment_eq_signedFiberCoeff_sum R q

/--
Forcing a context `I` leaves the residual free signed fiber system `S \ I`,
whose integrated conditional signed fiber spectrum is the common-prefix kernel.
-/
theorem conditional_context_kernel_eq_signedFiberCoeff_sum
    (S I : Finset ℕ) :
    commonPrefixKernel (S \ I) (subsetSum I) =
      ∑ m ∈ (S \ I).powerset.image subsetSum,
        signedFiberCoeff (S \ I) m /
          (1 + (((m + subsetSum I : ℕ) : ℝ))) := by
  exact commonPrefixKernel_eq_signedFiberCoeff_sum (S \ I) (subsetSum I)

/--
Exact signed marginal expansion over a disjoint perturbation.
-/
theorem phaseIntegral_union_eq_sum_commonPrefixKernel
    {R Q : Finset ℕ} (hRQ : Disjoint R Q) :
    phaseIntegral (R ∪ Q) =
      ∑ L ∈ Q.powerset,
        subsetSign L * commonPrefixKernel R (subsetSum L) := by
  classical
  unfold phaseIntegral commonPrefixKernel
  have hprod :
      ∀ u : ℝ,
        phaseProduct (R ∪ Q) u =
          phaseProduct R u * phaseProduct Q u := by
    intro u
    unfold phaseProduct
    rw [Finset.prod_union hRQ]
  calc
    (∫ u in (0 : ℝ)..1, phaseProduct (R ∪ Q) u)
        =
      ∫ u in (0 : ℝ)..1,
        phaseProduct R u * phaseProduct Q u := by
          apply intervalIntegral.integral_congr
          intro u _hu
          rw [hprod u]
    _ =
      ∫ u in (0 : ℝ)..1,
        phaseProduct R u *
          (∑ L ∈ Q.powerset, subsetSign L * u ^ subsetSum L) := by
          apply intervalIntegral.integral_congr
          intro u _hu
          dsimp
          rw [phaseProduct_powersetExpansion Q u]
    _ =
      ∫ u in (0 : ℝ)..1,
        ∑ L ∈ Q.powerset,
          subsetSign L * (phaseProduct R u * u ^ subsetSum L) := by
          apply intervalIntegral.integral_congr
          intro u _hu
          dsimp
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro L _hL
          ring
    _ =
      ∑ L ∈ Q.powerset,
        ∫ u in (0 : ℝ)..1,
          subsetSign L * (phaseProduct R u * u ^ subsetSum L) := by
          rw [intervalIntegral.integral_finset_sum]
          intro L _hL
          exact (continuous_const.mul
            ((continuous_phaseProduct R).mul
              (continuous_id.pow (subsetSum L)))).intervalIntegrable 0 1
    _ =
      ∑ L ∈ Q.powerset,
        subsetSign L * commonPrefixKernel R (subsetSum L) := by
          refine Finset.sum_congr rfl ?_
          intro L _hL
          rw [commonPrefixKernel, intervalIntegral.integral_const_mul]

end ProductInvariants
