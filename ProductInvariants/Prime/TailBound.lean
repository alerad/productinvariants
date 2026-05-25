import ProductInvariants.Prime.Convergence
import ProductInvariants.Prime.ErrorBounds
import Mathlib.NumberTheory.SumPrimeReciprocals

namespace ProductInvariants

/-- The sharp tail kernel from the factor `1 - u^2`. -/
noncomputable def primeTailKernel (q : ℕ) : ℝ :=
  (2 : ℝ) / ((q + 1) * (q + 3))

/-- The infinite tail of primes strictly above `N`. -/
abbrev PrimeTail (N : ℕ) :=
  {p : ℕ // Nat.Prime p ∧ N < p}

/-- The sharp tail kernel is nonnegative. -/
theorem primeTailKernel_nonneg (q : ℕ) :
    0 ≤ primeTailKernel q := by
  unfold primeTailKernel
  positivity

theorem primeTailKernel_le_two_mul_rpow_neg_two (p : PrimeTail N) :
    primeTailKernel p.1 ≤ 2 * (p.1 : ℝ) ^ (-2 : ℝ) := by
  have hp_pos_nat : 0 < p.1 := p.2.1.pos
  have hp_pos : (0 : ℝ) < p.1 := by exact_mod_cast hp_pos_nat
  have hden_pos : (0 : ℝ) < ((p.1 : ℝ) + 1) * ((p.1 : ℝ) + 3) := by
    positivity
  have hsquare_pos : (0 : ℝ) < (p.1 : ℝ) ^ 2 := sq_pos_of_ne_zero (by positivity)
  have hden_ge :
      (p.1 : ℝ) ^ 2 ≤
        ((p.1 : ℝ) + 1) * ((p.1 : ℝ) + 3) := by
    ring_nf
    nlinarith [hp_pos]
  unfold primeTailKernel
  have hrecip :
      (1 : ℝ) /
          (((p.1 : ℝ) + 1) * ((p.1 : ℝ) + 3)) ≤
        1 / ((p.1 : ℝ) ^ 2) :=
    one_div_le_one_div_of_le hsquare_pos hden_ge
  have hrpow : (p.1 : ℝ) ^ (-2 : ℝ) = 1 / (p.1 : ℝ) ^ 2 := by
    rw [Real.rpow_neg hp_pos.le]
    rw [div_eq_mul_inv, one_mul]
    norm_num
  calc
    (2 : ℝ) / (((p.1 : ℝ) + 1) * ((p.1 : ℝ) + 3)) =
        2 * (1 / (((p.1 : ℝ) + 1) * ((p.1 : ℝ) + 3))) := by
      ring_nf
    _ ≤ 2 * (1 / (p.1 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hrecip (by norm_num)
    _ = 2 * (p.1 : ℝ) ^ (-2 : ℝ) := by rw [hrpow]

theorem summable_primeTailKernel (N : ℕ) :
    Summable fun p : PrimeTail N => primeTailKernel p.1 := by
  have hpow :
      Summable fun p : PrimeTail N => 2 * (p.1 : ℝ) ^ (-2 : ℝ) := by
    exact (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).subtype
      {n : ℕ | Nat.Prime n ∧ N < n} |>.mul_left 2
  exact hpow.of_nonneg_of_le
    (fun p => primeTailKernel_nonneg p.1)
    (fun p => primeTailKernel_le_two_mul_rpow_neg_two p)

theorem primeSetUpTo_mono :
    Monotone primeSetUpTo := by
  intro N M hNM
  simpa [primeSetUpTo] using truncationSet_mono Nat.Prime hNM

theorem two_mem_primeSetUpTo {N : ℕ} (hN : 2 ≤ N) :
    2 ∈ primeSetUpTo N := by
  unfold primeSetUpTo truncationSet
  simp [hN, Nat.prime_two]

theorem mem_primeSetUpTo_iff {p N : ℕ} :
    p ∈ primeSetUpTo N ↔ 0 < p ∧ Nat.Prime p ∧ p ≤ N := by
  unfold primeSetUpTo truncationSet
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2, h.1⟩
  · intro h
    exact ⟨h.2.2, h.1, h.2.1⟩

theorem prime_of_mem_primeSetUpTo {p N : ℕ}
    (hp : p ∈ primeSetUpTo N) :
    Nat.Prime p :=
  (mem_primeSetUpTo_iff.mp hp).2.1

theorem lt_of_mem_primeSetUpTo_sdiff {p N M : ℕ}
    (hp : p ∈ primeSetUpTo M \ primeSetUpTo N) :
    N < p := by
  have hpM : p ∈ primeSetUpTo M := (Finset.mem_sdiff.mp hp).1
  have hpN : p ∉ primeSetUpTo N := (Finset.mem_sdiff.mp hp).2
  have hpprime : Nat.Prime p := prime_of_mem_primeSetUpTo hpM
  by_contra hlt
  have hp_le_N : p ≤ N := Nat.le_of_not_lt hlt
  exact hpN (mem_primeSetUpTo_iff.mpr ⟨hpprime.pos, hpprime, hp_le_N⟩)

/-- The finite newly added prime tail, indexed as a subset of the infinite tail. -/
noncomputable def primeTailFinset (N M : ℕ) : Finset (PrimeTail N) :=
  (primeSetUpTo M \ primeSetUpTo N).attach.map
    ⟨fun p =>
      ⟨p.1, prime_of_mem_primeSetUpTo (Finset.mem_sdiff.mp p.2).1,
        lt_of_mem_primeSetUpTo_sdiff p.2⟩,
      by
        intro a b h
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext h⟩

theorem sum_primeTailFinset_eq_sdiff (N M : ℕ) :
    (∑ p ∈ primeTailFinset N M, primeTailKernel p.1) =
      ∑ q ∈ primeSetUpTo M \ primeSetUpTo N, primeTailKernel q := by
  unfold primeTailFinset
  rw [Finset.sum_map]
  exact Finset.sum_attach (primeSetUpTo M \ primeSetUpTo N) primeTailKernel

/--
Finite sharp prime-tail law.

For `2 ≤ N ≤ M`, the drop from the `N`-prime truncation to the `M`-prime
truncation is controlled by the square-tail kernel over the newly added
primes.
-/
theorem prime_phase_finite_tail_bound {N M : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) :
    phaseIntegral (primeSetUpTo N) - phaseIntegral (primeSetUpTo M) ≤
      ∑ q ∈ primeSetUpTo M \ primeSetUpTo N, primeTailKernel q := by
  simpa [primeTailKernel] using
    sharp_error_bound_two_over
      (S := primeSetUpTo N)
      (T := primeSetUpTo M)
      (primeSetUpTo_mono hNM)
      (two_mem_primeSetUpTo hN)

/-- Finite sharp prime-tail law indexed inside the infinite prime tail. -/
theorem prime_phase_finite_tail_bound_subtype {N M : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) :
    phaseIntegral (primeSetUpTo N) - phaseIntegral (primeSetUpTo M) ≤
      ∑ p ∈ primeTailFinset N M, primeTailKernel p.1 := by
  rw [sum_primeTailFinset_eq_sdiff]
  exact prime_phase_finite_tail_bound hN hNM

/--
Finite prime-tail law bounded by the full infinite prime tail, assuming the
tail kernel is summable on primes above `N`.
-/
theorem prime_phase_finite_tail_bound_tsum {N M : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (hsum : Summable fun p : PrimeTail N => primeTailKernel p.1) :
    phaseIntegral (primeSetUpTo N) - phaseIntegral (primeSetUpTo M) ≤
      ∑' p : PrimeTail N, primeTailKernel p.1 := by
  exact (prime_phase_finite_tail_bound_subtype hN hNM).trans
    (hsum.sum_le_tsum (primeTailFinset N M)
      (fun p _hp => primeTailKernel_nonneg p.1))

/--
Infinite prime-tail law.

For every `N ≥ 2`, the defect between the `N`-prime truncation and the limiting
The prime product-integral drop is bounded by the full square-type prime tail,
provided that tail
kernel is summable.

The remaining analytic-number-theory step is to estimate this `tsum`, e.g. by
comparison with the prime-square tail.
-/
theorem prime_phase_tail_bound_of_summable {N : ℕ}
    (hN : 2 ≤ N)
    (hsum : Summable fun p : PrimeTail N => primeTailKernel p.1) :
    phaseIntegral (primeSetUpTo N) - Lambda ≤
      ∑' p : PrimeTail N, primeTailKernel p.1 := by
  have hlim :
      Filter.Tendsto
        (fun M => phaseIntegral (primeSetUpTo N) - phaseIntegral (primeSetUpTo M))
        Filter.atTop
        (nhds (phaseIntegral (primeSetUpTo N) - Lambda)) :=
    tendsto_const_nhds.sub prime_truncations_tendsto_Lambda
  exact le_of_tendsto hlim
    (Filter.eventually_atTop.2
      ⟨N, fun M hNM => prime_phase_finite_tail_bound_tsum hN hNM hsum⟩)

/--
Prime-tail law with the summability of the square-type kernel discharged by
comparison to the convergent `p^{-2}` tail.
-/
theorem prime_phase_tail_bound {N : ℕ}
    (hN : 2 ≤ N) :
    phaseIntegral (primeSetUpTo N) - Lambda ≤
      ∑' p : PrimeTail N, primeTailKernel p.1 :=
  prime_phase_tail_bound_of_summable hN (summable_primeTailKernel N)

end ProductInvariants
