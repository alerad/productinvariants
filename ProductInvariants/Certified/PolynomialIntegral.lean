import ProductInvariants.Prime.TailBound
import Mathlib.RingTheory.Polynomial.Basic

open MeasureTheory intervalIntegral Polynomial

set_option maxRecDepth 100000

namespace ProductInvariants.Certified

/-- The directed prime constant is below every finite prime truncation. -/
theorem Lambda_le_prime_truncation (N : ℕ) :
    Lambda ≤ phaseIntegral (primeSetUpTo N) := by
  simpa [Lambda, primeSetUpTo] using
    directedPhaseIntegral_le_truncation Nat.Prime N

noncomputable def phasePoly (S : Finset ℕ) : Polynomial ℝ :=
  ∏ n ∈ S, (1 - Polynomial.X ^ n)

noncomputable def polyIntegral (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i / ((i : ℝ) + 1)

theorem integral_polynomial_eq_polyIntegral (p : Polynomial ℝ) :
    (∫ u in (0 : ℝ)..1, p.eval u) = polyIntegral p := by
  unfold polyIntegral
  have hfun : (fun u : ℝ => p.eval u) =
      fun u : ℝ => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * u ^ i := by
    funext u
    rw [Polynomial.eval_eq_sum_range]
  rw [hfun]
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [intervalIntegral.integral_const_mul]
    rw [integral_pow]
    have hpow : (1 : ℝ) ^ (i + 1) - (0 : ℝ) ^ (i + 1) = 1 := by
      rw [one_pow, zero_pow (Nat.succ_ne_zero i), sub_zero]
    rw [hpow]
    rw [div_eq_mul_inv]
    ring
  · intro i _hi
    exact ((continuous_const.mul (continuous_id.pow i))).intervalIntegrable 0 1

theorem phasePoly_eval (S : Finset ℕ) (u : ℝ) :
    (phasePoly S).eval u = phaseProduct S u := by
  unfold phasePoly phaseProduct
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl ?_
  intro n _hn
  simp

theorem phaseIntegral_eq_polyIntegral (S : Finset ℕ) :
    phaseIntegral S = polyIntegral (phasePoly S) := by
  unfold phaseIntegral
  rw [← integral_polynomial_eq_polyIntegral (phasePoly S)]
  apply intervalIntegral.integral_congr
  intro u _hu
  exact (phasePoly_eval S u).symm

/-! ## Computable integer-polynomial certificates -/

abbrev IPoly := List ℤ

def IPoly.evalFrom : IPoly → ℕ → ℝ → ℝ
  | [], _k, _u => 0
  | c :: cs, k, u => (c : ℝ) * u ^ k + IPoly.evalFrom cs (k + 1) u

def IPoly.integralFrom : IPoly → ℕ → ℚ
  | [], _k => 0
  | c :: cs, k => (c : ℚ) / ((k : ℚ) + 1) + IPoly.integralFrom cs (k + 1)

def IPoly.neg : IPoly → IPoly
  | [] => []
  | c :: cs => (-c) :: IPoly.neg cs

def IPoly.sub : IPoly → IPoly → IPoly
  | [], q => IPoly.neg q
  | p, [] => p
  | c :: cs, d :: ds => (c - d) :: IPoly.sub cs ds

def IPoly.shift (m : ℕ) (p : IPoly) : IPoly :=
  List.replicate m 0 ++ p

def IPoly.mulOneMinus (p : IPoly) (m : ℕ) : IPoly :=
  IPoly.sub p (IPoly.shift m p)

def IPoly.ofFactors : List ℕ → IPoly
  | [] => [1]
  | m :: ms => IPoly.mulOneMinus (IPoly.ofFactors ms) m

def primeFactorsUpTo (N : ℕ) : List ℕ :=
  (primeSetUpTo N).sort (· ≤ ·)

def primePhaseIPoly (N : ℕ) : IPoly :=
  IPoly.ofFactors (primeFactorsUpTo N)

def primePhaseIntegralRat (N : ℕ) : ℚ :=
  IPoly.integralFrom (primePhaseIPoly N) 0

def oddPrimeFactorsUpTo (N : ℕ) : List ℕ :=
  ((primeSetUpTo N).filter (fun p => p ≠ 2)).sort (· ≤ ·)

def oddPrimePhaseIPoly (N : ℕ) : IPoly :=
  IPoly.ofFactors (oddPrimeFactorsUpTo N)

def sandwichErrorIPoly (N m : ℕ) : IPoly :=
  IPoly.shift m (oddPrimePhaseIPoly N)

def sandwichErrorIntegralRat (N m : ℕ) : ℚ :=
  IPoly.integralFrom (sandwichErrorIPoly N m) 0

def sandwichLowerRat (N m : ℕ) : ℚ :=
  primePhaseIntegralRat N - sandwichErrorIntegralRat N m

theorem IPoly.evalFrom_neg (p : IPoly) (k : ℕ) (u : ℝ) :
    IPoly.evalFrom (IPoly.neg p) k u = -IPoly.evalFrom p k u := by
  induction p generalizing k with
  | nil => simp [IPoly.neg, IPoly.evalFrom]
  | cons c cs ih =>
      simp [IPoly.neg, IPoly.evalFrom, ih]
      ring

theorem IPoly.evalFrom_sub (p q : IPoly) (k : ℕ) (u : ℝ) :
    IPoly.evalFrom (IPoly.sub p q) k u =
      IPoly.evalFrom p k u - IPoly.evalFrom q k u := by
  induction p generalizing q k with
  | nil =>
      simp [IPoly.sub, IPoly.evalFrom, IPoly.evalFrom_neg]
  | cons c cs ih =>
      cases q with
      | nil => simp [IPoly.sub, IPoly.evalFrom]
      | cons d ds =>
          simp [IPoly.sub, IPoly.evalFrom, ih]
          ring

set_option linter.flexible false in
theorem IPoly.evalFrom_shift_add (p : IPoly) (m k : ℕ) (u : ℝ) :
    IPoly.evalFrom (IPoly.shift m p) k u = IPoly.evalFrom p (k + m) u := by
  induction m generalizing k with
  | zero => simp [IPoly.shift]
  | succ m ih =>
      change IPoly.evalFrom (0 :: (List.replicate m 0 ++ p)) k u =
        IPoly.evalFrom p (k + (m + 1)) u
      simp [IPoly.evalFrom]
      change IPoly.evalFrom (IPoly.shift m p) (k + 1) u =
        IPoly.evalFrom p (k + (m + 1)) u
      rw [ih (k + 1)]
      congr 1
      omega

set_option linter.flexible false in
theorem IPoly.evalFrom_add_eq_pow_mul (p : IPoly) (m k : ℕ) (u : ℝ) :
    IPoly.evalFrom p (k + m) u = u ^ m * IPoly.evalFrom p k u := by
  induction p generalizing k with
  | nil =>
      simp [IPoly.evalFrom]
  | cons c cs ih =>
      simp [IPoly.evalFrom]
      rw [pow_add]
      have hidx : k + m + 1 = k + 1 + m := by omega
      rw [hidx, ih (k + 1)]
      ring

theorem IPoly.evalFrom_shift_zero (p : IPoly) (m : ℕ) (u : ℝ) :
    IPoly.evalFrom (IPoly.shift m p) 0 u = u ^ m * IPoly.evalFrom p 0 u := by
  rw [IPoly.evalFrom_shift_add]
  simpa using IPoly.evalFrom_add_eq_pow_mul p m 0 u

theorem IPoly.evalFrom_mulOneMinus (p : IPoly) (m : ℕ) (u : ℝ) :
    IPoly.evalFrom (IPoly.mulOneMinus p m) 0 u =
      IPoly.evalFrom p 0 u * (1 - u ^ m) := by
  unfold IPoly.mulOneMinus
  rw [IPoly.evalFrom_sub, IPoly.evalFrom_shift_zero]
  ring

theorem IPoly.evalFrom_ofFactors (factors : List ℕ) (u : ℝ) :
    IPoly.evalFrom (IPoly.ofFactors factors) 0 u =
      (factors.map fun m => (1 - u ^ m)).prod := by
  induction factors with
  | nil => simp [IPoly.ofFactors, IPoly.evalFrom]
  | cons m ms ih =>
      simp [IPoly.ofFactors, IPoly.evalFrom_mulOneMinus, ih]
      ring

set_option linter.flexible false in
theorem IPoly.continuous_evalFrom (p : IPoly) (k : ℕ) :
    Continuous (fun u : ℝ => IPoly.evalFrom p k u) := by
  induction p generalizing k with
  | nil =>
      change Continuous (fun _ : ℝ => (0 : ℝ))
      exact continuous_const
  | cons c cs ih =>
      simp [IPoly.evalFrom]
      exact (continuous_const.mul (continuous_id.pow k)).add (ih (k + 1))

set_option linter.flexible false in
theorem IPoly.integral_evalFrom (p : IPoly) (k : ℕ) :
    (∫ u in (0 : ℝ)..1, IPoly.evalFrom p k u) =
      (IPoly.integralFrom p k : ℝ) := by
  induction p generalizing k with
  | nil =>
      simp [IPoly.evalFrom, IPoly.integralFrom]
  | cons c cs ih =>
      simp [IPoly.evalFrom, IPoly.integralFrom]
      have hmono :
          (∫ u in (0 : ℝ)..1, (c : ℝ) * u ^ k) =
            (c : ℝ) / ((k : ℝ) + 1) := by
        rw [intervalIntegral.integral_const_mul]
        rw [integral_pow]
        have hpow : (1 : ℝ) ^ (k + 1) - (0 : ℝ) ^ (k + 1) = 1 := by
          rw [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
        rw [hpow]
        rw [div_eq_mul_inv]
        ring
      rw [intervalIntegral.integral_add]
      · rw [hmono, ih]
      · exact ((continuous_const.mul (continuous_id.pow k))).intervalIntegrable 0 1
      · exact (IPoly.continuous_evalFrom cs (k + 1)).intervalIntegrable 0 1

theorem primePhaseIPoly_eval (N : ℕ) (u : ℝ) :
    IPoly.evalFrom (primePhaseIPoly N) 0 u = phaseProduct (primeSetUpTo N) u := by
  unfold primePhaseIPoly primeFactorsUpTo
  rw [IPoly.evalFrom_ofFactors]
  have hperm :
      @List.Perm ℝ
        (((primeSetUpTo N).sort (· ≤ ·)).map (fun n => (1 - u ^ n)))
        ((primeSetUpTo N).toList.map (fun n => (1 - u ^ n))) :=
    (Finset.sort_perm_toList (primeSetUpTo N) (· ≤ ·)).map _
  have hprod := hperm.prod_eq
  rw [hprod]
  simp [phaseProduct]

theorem oddPrimePhaseIPoly_eval (N : ℕ) (u : ℝ) :
    IPoly.evalFrom (oddPrimePhaseIPoly N) 0 u =
      phaseProduct ((primeSetUpTo N).filter (fun p => p ≠ 2)) u := by
  unfold oddPrimePhaseIPoly oddPrimeFactorsUpTo
  rw [IPoly.evalFrom_ofFactors]
  have hperm :
      @List.Perm ℝ
        ((((primeSetUpTo N).filter (fun p => p ≠ 2)).sort (· ≤ ·)).map (fun n => (1 - u ^ n)))
        (((primeSetUpTo N).filter (fun p => p ≠ 2)).toList.map
          (fun n => (1 - u ^ n))) := by
    exact (Finset.sort_perm_toList ((primeSetUpTo N).filter (fun p => p ≠ 2)) (· ≤ ·)).map _
  have hprod := hperm.prod_eq
  rw [hprod]
  simp [phaseProduct]

theorem phaseIntegral_primeSetUpTo_eq_rat (N : ℕ) :
    phaseIntegral (primeSetUpTo N) = (primePhaseIntegralRat N : ℝ) := by
  unfold phaseIntegral primePhaseIntegralRat
  rw [← IPoly.integral_evalFrom (primePhaseIPoly N) 0]
  apply intervalIntegral.integral_congr
  intro u _hu
  exact (primePhaseIPoly_eval N u).symm

noncomputable def sandwichLowerFun (N m : ℕ) (u : ℝ) : ℝ :=
  phaseProduct (primeSetUpTo N) u -
    u ^ m * phaseProduct ((primeSetUpTo N).filter (fun p => p ≠ 2)) u

theorem sandwichErrorIPoly_eval (N m : ℕ) (u : ℝ) :
    IPoly.evalFrom (sandwichErrorIPoly N m) 0 u =
      u ^ m * phaseProduct ((primeSetUpTo N).filter (fun p => p ≠ 2)) u := by
  unfold sandwichErrorIPoly
  rw [IPoly.evalFrom_shift_zero, oddPrimePhaseIPoly_eval]

theorem integral_sandwichLowerFun_eq_rat (N m : ℕ) :
    (∫ u in (0 : ℝ)..1, sandwichLowerFun N m u) =
      (sandwichLowerRat N m : ℝ) := by
  have hmain :
      (∫ u in (0 : ℝ)..1, phaseProduct (primeSetUpTo N) u) =
        (primePhaseIntegralRat N : ℝ) := by
    simpa [phaseIntegral] using phaseIntegral_primeSetUpTo_eq_rat N
  have herror :
      (∫ u in (0 : ℝ)..1,
          u ^ m * phaseProduct ((primeSetUpTo N).filter (fun p => p ≠ 2)) u) =
        (sandwichErrorIntegralRat N m : ℝ) := by
    unfold sandwichErrorIntegralRat
    rw [← IPoly.integral_evalFrom (sandwichErrorIPoly N m) 0]
    apply intervalIntegral.integral_congr
    intro u _hu
    exact (sandwichErrorIPoly_eval N m u).symm
  unfold sandwichLowerFun
  rw [intervalIntegral.integral_sub]
  · rw [hmain, herror]
    unfold sandwichLowerRat
    norm_num
  · exact intervalIntegrable_phaseProduct (primeSetUpTo N)
  · exact ((continuous_id.pow m).mul
      (continuous_phaseProduct ((primeSetUpTo N).filter (fun p => p ≠ 2)))).intervalIntegrable 0 1

theorem geometric_telescope_finite (m n : ℕ) (u : ℝ) :
    (1 - u ^ 2) * ∑ k ∈ Finset.range n, u ^ (m + 2 * k) =
      u ^ m - u ^ (m + 2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have h1 :
          (1 - u ^ 2) * u ^ (m + 2 * n) =
            u ^ (m + 2 * n) - u ^ (m + 2 * n) * u ^ 2 := by
        ring
      rw [h1, ← pow_add]
      ring_nf

theorem telescope_sum_le (m : ℕ) (K : Finset ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u ^ 2) * ∑ k ∈ K, u ^ (m + 2 * k) ≤ u ^ m := by
  by_cases hK : K = ∅
  · simp [hK, pow_nonneg hu0]
  · have ⟨M, hM⟩ := Finset.exists_max_image K id (Finset.nonempty_of_ne_empty hK)
    let n := M + 1
    have hK_sub : K ⊆ Finset.range n := by
      intro k hk
      simp only [Finset.mem_range]
      have h := hM.2 k hk
      simp only [id] at h
      exact Nat.lt_add_one_of_le h
    have h_sum_le :
        ∑ k ∈ K, u ^ (m + 2 * k) ≤
          ∑ k ∈ Finset.range n, u ^ (m + 2 * k) :=
      Finset.sum_le_sum_of_subset_of_nonneg hK_sub
        (fun _ _ _ => pow_nonneg hu0 _)
    have h_telescope := geometric_telescope_finite m n u
    have h_u2_le : u ^ 2 ≤ 1 := by
      calc
        u ^ 2 = u * u := sq u
        _ ≤ 1 * 1 := mul_le_mul hu1 hu1 hu0 (by linarith)
        _ = 1 := one_mul 1
    have h_1_sub_nonneg : 0 ≤ 1 - u ^ 2 := by linarith
    calc
      (1 - u ^ 2) * ∑ k ∈ K, u ^ (m + 2 * k)
          ≤ (1 - u ^ 2) * ∑ k ∈ Finset.range n, u ^ (m + 2 * k) :=
            mul_le_mul_of_nonneg_left h_sum_le h_1_sub_nonneg
      _ = u ^ m - u ^ (m + 2 * n) := h_telescope
      _ ≤ u ^ m := by linarith [pow_nonneg hu0 (m + 2 * n)]

theorem prime_gt_two_odd {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p) : Odd p := by
  rcases Nat.Prime.eq_two_or_odd hp with hp_eq | hp_odd
  · omega
  · exact Nat.odd_iff.mpr hp_odd

theorem odd_ge_form {m p : ℕ} (hm : Odd m) (hp : Odd p) (hpm : m ≤ p) :
    ∃ k, p = m + 2 * k := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hp
  use b - a
  omega

theorem telescope_odd_sum_bound_from {m : ℕ} (hm : Odd m) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Odd p ∧ m ≤ p)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u ^ 2) * ∑ p ∈ S, u ^ p ≤ u ^ m := by
  let f : ℕ → ℕ := fun p => (p - m) / 2
  have h_pow_eq : ∀ p ∈ S, u ^ p = u ^ (m + 2 * f p) := by
    intro p hp
    obtain ⟨hp_odd, hp_ge⟩ := hS p hp
    obtain ⟨k, hk⟩ := odd_ge_form hm hp_odd hp_ge
    have hf : f p = k := by
      change (p - m) / 2 = k
      omega
    have hp_form : p = m + 2 * f p := by rw [hf, hk]
    exact congrArg (u ^ ·) hp_form
  have h_f_inj : Set.InjOn f S := by
    intro p₁ hp₁ p₂ hp₂ hf_eq
    obtain ⟨hp₁_odd, hp₁_ge⟩ := hS p₁ hp₁
    obtain ⟨hp₂_odd, hp₂_ge⟩ := hS p₂ hp₂
    obtain ⟨k₁, hk₁⟩ := odd_ge_form hm hp₁_odd hp₁_ge
    obtain ⟨k₂, hk₂⟩ := odd_ge_form hm hp₂_odd hp₂_ge
    have hf₁ : f p₁ = k₁ := by
      change (p₁ - m) / 2 = k₁
      omega
    have hf₂ : f p₂ = k₂ := by
      change (p₂ - m) / 2 = k₂
      omega
    rw [hf₁, hf₂] at hf_eq
    omega
  have h_sum_eq : ∑ p ∈ S, u ^ p = ∑ k ∈ S.image f, u ^ (m + 2 * k) := by
    conv_lhs => rw [Finset.sum_congr rfl h_pow_eq]
    show ∑ p ∈ S, u ^ (m + 2 * f p) = ∑ k ∈ S.image f, u ^ (m + 2 * k)
    rw [Finset.sum_image h_f_inj]
  rw [h_sum_eq]
  exact telescope_sum_le m (S.image f) u hu0 hu1

theorem sandwichLowerFun_pointwise_of_tail_ge {N m : ℕ} (hm : Odd m) (hN : 2 ≤ N)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p)
    (S : Finset ℕ)
    (hbase : primeSetUpTo N ⊆ S) (hS_primes : ∀ p ∈ S, Nat.Prime p)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    sandwichLowerFun N m u ≤ phaseProduct S u := by
  let B := primeSetUpTo N
  let O := B.filter (fun p => p ≠ 2)
  let T := S \ B
  let R := phaseProduct O u
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ 1 := hu.2
  have hsplit : phaseProduct S u = phaseProduct B u * phaseProduct T u := by
    unfold phaseProduct T B
    rw [← Finset.prod_union Finset.disjoint_sdiff]
    congr 1
    exact (Finset.union_sdiff_of_subset hbase).symm
  have hB2 : 2 ∈ B := by
    simp [B, truncationSet, hN, Nat.prime_two]
  have hB_eq : B = insert 2 O := by
    ext p
    by_cases hp : p = 2
    · subst hp
      simp [O, hB2]
    · simp [O, hp]
  have hP_eq : phaseProduct B u = (1 - u ^ 2) * R := by
    rw [hB_eq]
    unfold R O phaseProduct
    simp
  have hR_nonneg : 0 ≤ R := by
    unfold R
    exact phaseProduct_nonneg_on_Icc O hu
  have hmain : (1 - u ^ 2) * (1 - phaseProduct T u) ≤ u ^ m := by
    have h_weier : 1 - phaseProduct T u ≤ ∑ p ∈ T, u ^ p := by
      unfold phaseProduct
      simpa [sub_eq_add_neg] using
        (one_sub_prod_le_sum_one_sub T (fun q => 1 - u ^ q)
          (fun q _hq => one_sub_pow_nonneg_of_mem_Icc ⟨hu0, hu1⟩ q)
          (fun q _hq => one_sub_pow_le_one_of_mem_Icc ⟨hu0, hu1⟩ q))
    have h_tail : ∀ p ∈ T, Odd p ∧ m ≤ p := by
      intro p hp
      have hpS : p ∈ S := (Finset.mem_sdiff.mp hp).1
      have hp_notB : p ∉ B := (Finset.mem_sdiff.mp hp).2
      have hp_prime : Nat.Prime p := hS_primes p hpS
      have hp_gt : N < p := by
        by_contra hle
        push Not at hle
        have hpB : p ∈ B := by
          simp [B, truncationSet, hp_prime, hp_prime.pos,
            Nat.lt_succ_of_le hle]
        exact hp_notB hpB
      have hp_odd : Odd p := prime_gt_two_odd hp_prime (lt_of_le_of_lt hN hp_gt)
      exact ⟨hp_odd, htail_ge p hp_prime hp_gt⟩
    have h_bound :
        (1 - u ^ 2) * ∑ p ∈ T, u ^ p ≤ u ^ m :=
      telescope_odd_sum_bound_from hm T h_tail u hu0 hu1
    have h_1_sub_u2_nonneg : 0 ≤ 1 - u ^ 2 := by
      have : u ^ 2 ≤ 1 := by
        exact pow_le_one₀ hu0 hu1
      linarith
    exact (mul_le_mul_of_nonneg_left h_weier h_1_sub_u2_nonneg).trans h_bound
  unfold sandwichLowerFun
  rw [hsplit, hP_eq]
  have hscalar : (1 - u ^ 2) - u ^ m ≤ (1 - u ^ 2) * phaseProduct T u := by
    nlinarith [hmain]
  calc (1 - u ^ 2) * R - u ^ m * R
      = ((1 - u ^ 2) - u ^ m) * R := by ring
    _ ≤ ((1 - u ^ 2) * phaseProduct T u) * R := by
      exact mul_le_mul_of_nonneg_right hscalar hR_nonneg
    _ = (1 - u ^ 2) * R * phaseProduct T u := by ring

theorem sandwichLowerFun_101_103_le_prime_truncation (M : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    sandwichLowerFun 101 103 u ≤ phaseProduct (primeSetUpTo M) u := by
  let S := primeSetUpTo M ∪ primeSetUpTo 101
  have hpoint : sandwichLowerFun 101 103 u ≤ phaseProduct S u := by
    apply sandwichLowerFun_pointwise_of_tail_ge (N := 101) (m := 103) (by decide) (by norm_num)
    · intro p hp_prime hp_gt
      have hp_ge_102 : 102 ≤ p := Nat.succ_le_of_lt hp_gt
      rcases Nat.lt_or_eq_of_le hp_ge_102 with hp102 | hp102
      · exact Nat.succ_le_of_lt hp102
      · exfalso
        subst p
        exact (by decide : ¬ Nat.Prime 102) hp_prime
    · exact Finset.subset_union_right
    · intro p hp
      rcases Finset.mem_union.mp hp with hpM | hp101
      · simpa [primeSetUpTo, truncationSet] using (Finset.mem_filter.mp hpM).2.2
      · simpa [primeSetUpTo, truncationSet] using (Finset.mem_filter.mp hp101).2.2
    · exact hu
  exact hpoint.trans (phaseProduct_antitone Finset.subset_union_left hu)

theorem sandwichLowerFun_le_prime_truncation_of_tail_ge {N m : ℕ}
    (hm : Odd m) (hN : 2 ≤ N)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p)
    (M : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    sandwichLowerFun N m u ≤ phaseProduct (primeSetUpTo M) u := by
  let S := primeSetUpTo M ∪ primeSetUpTo N
  have hpoint : sandwichLowerFun N m u ≤ phaseProduct S u := by
    apply sandwichLowerFun_pointwise_of_tail_ge hm hN htail_ge
    · exact Finset.subset_union_right
    · intro p hp
      rcases Finset.mem_union.mp hp with hpM | hpN
      · simpa [primeSetUpTo, truncationSet] using (Finset.mem_filter.mp hpM).2.2
      · simpa [primeSetUpTo, truncationSet] using (Finset.mem_filter.mp hpN).2.2
    · exact hu
  exact hpoint.trans (phaseProduct_antitone Finset.subset_union_left hu)

theorem sandwichLowerRat_le_Lambda_of_tail_ge {N m : ℕ}
    (hm : Odd m) (hN : 2 ≤ N)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p) :
    (sandwichLowerRat N m : ℝ) ≤ Lambda := by
  rw [Lambda, directedPhaseIntegral]
  apply le_ciInf
  intro M
  have hf : IntervalIntegrable (fun u : ℝ => sandwichLowerFun N m u) volume 0 1 := by
    unfold sandwichLowerFun
    exact ((continuous_phaseProduct (primeSetUpTo N)).sub
      ((continuous_id.pow m).mul
        (continuous_phaseProduct ((primeSetUpTo N).filter (fun p => p ≠ 2)))))
      |>.intervalIntegrable 0 1
  have hle :
      (∫ u in (0 : ℝ)..1, sandwichLowerFun N m u) ≤
        phaseIntegral (primeSetUpTo M) := by
    unfold phaseIntegral
    exact intervalIntegral.integral_mono_on (by norm_num) hf
      (intervalIntegrable_phaseProduct (primeSetUpTo M))
      (fun u hu => sandwichLowerFun_le_prime_truncation_of_tail_ge hm hN htail_ge M hu)
  rw [integral_sandwichLowerFun_eq_rat] at hle
  exact hle

/-- The finite error integral used in the prime product-integral sandwich. -/
noncomputable def sandwichErrorIntegral (N m : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    u ^ m * phaseProduct ((primeSetUpTo N).filter (fun p => p ≠ 2)) u

theorem sandwichErrorIntegral_eq_rat (N m : ℕ) :
    sandwichErrorIntegral N m = (sandwichErrorIntegralRat N m : ℝ) := by
  unfold sandwichErrorIntegral sandwichErrorIntegralRat
  rw [← IPoly.integral_evalFrom (sandwichErrorIPoly N m) 0]
  apply intervalIntegral.integral_congr
  intro u _hu
  exact (sandwichErrorIPoly_eval N m u).symm

theorem phaseIntegral_sub_sandwichErrorIntegral_eq_rat (N m : ℕ) :
    phaseIntegral (primeSetUpTo N) - sandwichErrorIntegral N m =
      (sandwichLowerRat N m : ℝ) := by
  rw [phaseIntegral_primeSetUpTo_eq_rat, sandwichErrorIntegral_eq_rat]
  unfold sandwichLowerRat
  norm_num

/--
Prime product-integral sandwich.

If `m` is odd and every prime after `N` is at least `m`, then the infinite prime
phase is trapped between the finite prime truncation and the same truncation
minus the finite odd-prime error integral.
-/
theorem prime_phase_sandwich {N m : ℕ}
    (hN : 2 ≤ N)
    (hm : Odd m)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p) :
    phaseIntegral (primeSetUpTo N) - sandwichErrorIntegral N m ≤ Lambda ∧
      Lambda ≤ phaseIntegral (primeSetUpTo N) := by
  constructor
  · rw [phaseIntegral_sub_sandwichErrorIntegral_eq_rat]
    exact sandwichLowerRat_le_Lambda_of_tail_ge hm hN htail_ge
  · exact Lambda_le_prime_truncation N

/--
The same sandwich in the exact rational polynomial certificate form.
-/
theorem prime_phase_rational_certificate {N m : ℕ}
    (hN : 2 ≤ N)
    (hm : Odd m)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p) :
    (sandwichLowerRat N m : ℝ) ≤ Lambda ∧
      Lambda ≤ (primePhaseIntegralRat N : ℝ) := by
  constructor
  · exact sandwichLowerRat_le_Lambda_of_tail_ge hm hN htail_ge
  · have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo N) :=
      Lambda_le_prime_truncation N
    rw [phaseIntegral_primeSetUpTo_eq_rat] at hΛ
    exact hΛ

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_3_eq :
    primePhaseIntegralRat 3 = (7 : ℚ) / 12 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichErrorIntegralRat_3_5_eq :
    sandwichErrorIntegralRat 3 5 = (1 : ℚ) / 18 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_3_5_eq :
    sandwichLowerRat 3 5 = (19 : ℚ) / 36 := by
  native_decide

theorem sandwichLowerRat_3_5_le_Lambda :
    (sandwichLowerRat 3 5 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 3) (m := 5) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge4 : 4 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge4 with hp4 | hp4
  · exact Nat.succ_le_of_lt hp4
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp_prime

/-- Elementary rational separation of the prime limit from one half. -/
theorem Lambda_gt_one_half :
    (1 : ℝ) / 2 < Lambda := by
  have hcert := sandwichLowerRat_3_5_le_Lambda
  rw [sandwichLowerRat_3_5_eq] at hcert
  norm_num at hcert
  have hgt : (1 : ℝ) / 2 < (19 : ℝ) / 36 := by norm_num
  exact hgt.trans_le hcert

theorem Lambda_elementary_interval_3_5 :
    (19 : ℝ) / 36 ≤ Lambda ∧ Lambda ≤ (7 : ℝ) / 12 := by
  constructor
  · have hcert := sandwichLowerRat_3_5_le_Lambda
    rw [sandwichLowerRat_3_5_eq] at hcert
    norm_num at hcert
    exact hcert
  · have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 3) :=
      Lambda_le_prime_truncation 3
    rw [phaseIntegral_primeSetUpTo_eq_rat, primePhaseIntegralRat_3_eq] at hΛ
    norm_num at hΛ
    exact hΛ

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_5_eq :
    primePhaseIntegralRat 5 = (445 : ℚ) / 792 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_5_7_eq :
    sandwichLowerRat 5 7 = (1015 : ℚ) / 1872 := by
  native_decide

theorem sandwichLowerRat_5_7_le_Lambda :
    (sandwichLowerRat 5 7 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 5) (m := 7) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge6 : 6 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge6 with hp6 | hp6
  · exact Nat.succ_le_of_lt hp6
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 6) hp_prime

theorem Lambda_elementary_interval_5_7 :
    (1015 : ℝ) / 1872 ≤ Lambda ∧ Lambda ≤ (445 : ℝ) / 792 := by
  constructor
  · have hcert := sandwichLowerRat_5_7_le_Lambda
    rw [sandwichLowerRat_5_7_eq] at hcert
    norm_num at hcert
    exact hcert
  · have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 5) :=
      Lambda_le_prime_truncation 5
    rw [phaseIntegral_primeSetUpTo_eq_rat, primePhaseIntegralRat_5_eq] at hΛ
    norm_num at hΛ
    exact hΛ

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_7_eq :
    primePhaseIntegralRat 7 = (133 : ℚ) / 240 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_7_11_eq :
    sandwichLowerRat 7 11 = (4212299 : ℚ) / 7674480 := by
  native_decide

theorem sandwichLowerRat_7_11_le_Lambda :
    (sandwichLowerRat 7 11 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 7) (m := 11) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge8 : 8 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge8 with hp8 | hp8
  · have hp_ge9 : 9 ≤ p := Nat.succ_le_of_lt hp8
    rcases Nat.lt_or_eq_of_le hp_ge9 with hp9 | hp9
    · have hp_ge10 : 10 ≤ p := Nat.succ_le_of_lt hp9
      rcases Nat.lt_or_eq_of_le hp_ge10 with hp10 | hp10
      · exact Nat.succ_le_of_lt hp10
      · exfalso
        subst p
        exact (by decide : ¬ Nat.Prime 10) hp_prime
    · exfalso
      subst p
      exact (by decide : ¬ Nat.Prime 9) hp_prime
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 8) hp_prime

theorem Lambda_elementary_interval_7_11 :
    (4212299 : ℝ) / 7674480 ≤ Lambda ∧ Lambda ≤ (133 : ℝ) / 240 := by
  constructor
  · have hcert := sandwichLowerRat_7_11_le_Lambda
    rw [sandwichLowerRat_7_11_eq] at hcert
    norm_num at hcert
    exact hcert
  · have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 7) :=
      Lambda_le_prime_truncation 7
    rw [phaseIntegral_primeSetUpTo_eq_rat, primePhaseIntegralRat_7_eq] at hΛ
    norm_num at hΛ
    exact hΛ

theorem sandwichLowerRat_101_103_le_Lambda :
    (sandwichLowerRat 101 103 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 101) (m := 103) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge_102 : 102 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge_102 with hp102 | hp102
  · exact Nat.succ_le_of_lt hp102
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 102) hp_prime

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_101_lt :
    primePhaseIntegralRat 101 < (55065304 : ℚ) / 100000000 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_101_103_gt :
    (55065295 : ℚ) / 100000000 < sandwichLowerRat 101 103 := by
  native_decide

theorem Lambda_gt_55065295_div_1e8 :
    (55065295 : ℝ) / 100000000 < Lambda := by
  have hrat : ((55065295 : ℚ) / 100000000 : ℝ) <
      (sandwichLowerRat 101 103 : ℝ) := by
    exact_mod_cast sandwichLowerRat_101_103_gt
  norm_num at hrat ⊢
  exact hrat.trans_le sandwichLowerRat_101_103_le_Lambda

/-- Certified upper side of the `N = 101` computation. -/
theorem Lambda_lt_55065304_div_1e8 :
    Lambda < (55065304 : ℝ) / 100000000 := by
  have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 101) :=
    Lambda_le_prime_truncation 101
  rw [phaseIntegral_primeSetUpTo_eq_rat] at hΛ
  have hrat : (primePhaseIntegralRat 101 : ℝ) <
      ((55065304 : ℚ) / 100000000 : ℝ) := by
    exact_mod_cast primePhaseIntegralRat_101_lt
  norm_num at hrat ⊢
  exact lt_of_le_of_lt hΛ hrat

theorem Lambda_bounds_101 :
    (55065295 : ℝ) / 100000000 < Lambda ∧
      Lambda < (55065304 : ℝ) / 100000000 :=
  ⟨Lambda_gt_55065295_div_1e8, Lambda_lt_55065304_div_1e8⟩

theorem sandwichLowerRat_503_505_le_Lambda :
    (sandwichLowerRat 503 505 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 503) (m := 505) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge_504 : 504 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge_504 with hp504 | hp504
  · exact Nat.succ_le_of_lt hp504
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 504) hp_prime

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_503_lt :
    primePhaseIntegralRat 503 <
      (5506530112728432344854780 : ℚ) / 10000000000000000000000000 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_503_505_gt :
    (5506530112728420906200021 : ℚ) / 10000000000000000000000000 <
      sandwichLowerRat 503 505 := by
  native_decide

theorem Lambda_gt_5506530112728420906200021_div_1e25 :
    (5506530112728420906200021 : ℝ) / 10000000000000000000000000 < Lambda := by
  have hrat :
      ((5506530112728420906200021 : ℚ) / 10000000000000000000000000 : ℝ) <
        (sandwichLowerRat 503 505 : ℝ) := by
    exact_mod_cast sandwichLowerRat_503_505_gt
  norm_num at hrat ⊢
  exact hrat.trans_le sandwichLowerRat_503_505_le_Lambda

theorem Lambda_lt_5506530112728432344854780_div_1e25 :
    Lambda < (5506530112728432344854780 : ℝ) /
      10000000000000000000000000 := by
  have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 503) :=
    Lambda_le_prime_truncation 503
  rw [phaseIntegral_primeSetUpTo_eq_rat] at hΛ
  have hrat : (primePhaseIntegralRat 503 : ℝ) <
      ((5506530112728432344854780 : ℚ) / 10000000000000000000000000 : ℝ) := by
    exact_mod_cast primePhaseIntegralRat_503_lt
  norm_num at hrat ⊢
  exact lt_of_le_of_lt hΛ hrat

theorem Lambda_bounds_503 :
    (5506530112728420906200021 : ℝ) / 10000000000000000000000000 < Lambda ∧
      Lambda < (5506530112728432344854780 : ℝ) /
        10000000000000000000000000 :=
  ⟨Lambda_gt_5506530112728420906200021_div_1e25,
    Lambda_lt_5506530112728432344854780_div_1e25⟩

theorem sandwichLowerRat_1009_1011_le_Lambda :
    (sandwichLowerRat 1009 1011 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 1009) (m := 1011) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge_1010 : 1010 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge_1010 with hp1010 | hp1010
  · exact Nat.succ_le_of_lt hp1010
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 1010) hp_prime

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_1009_lt :
    primePhaseIntegralRat 1009 <
      (550653011272842963579465933094387203471136467695308801315764 : ℚ) / 10 ^ 60 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_1009_1011_gt :
    (550653011272842963574907227315784759883099490122684597014105 : ℚ) / 10 ^ 60 <
      sandwichLowerRat 1009 1011 := by
  native_decide

theorem Lambda_gt_550653011272842963574907227315784759883099490122684597014105_div_1e60 :
    (550653011272842963574907227315784759883099490122684597014105 : ℝ) / 10 ^ 60 <
      Lambda := by
  have hrat :
      ((550653011272842963574907227315784759883099490122684597014105 : ℚ) / 10 ^ 60 : ℝ) <
        (sandwichLowerRat 1009 1011 : ℝ) := by
    exact_mod_cast sandwichLowerRat_1009_1011_gt
  norm_num at hrat ⊢
  exact hrat.trans_le sandwichLowerRat_1009_1011_le_Lambda

theorem Lambda_lt_550653011272842963579465933094387203471136467695308801315764_div_1e60 :
    Lambda <
      (550653011272842963579465933094387203471136467695308801315764 : ℝ) / 10 ^ 60 := by
  have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 1009) :=
    Lambda_le_prime_truncation 1009
  rw [phaseIntegral_primeSetUpTo_eq_rat] at hΛ
  have hrat : (primePhaseIntegralRat 1009 : ℝ) <
      ((550653011272842963579465933094387203471136467695308801315764 : ℚ) / 10 ^ 60 : ℝ) := by
    exact_mod_cast primePhaseIntegralRat_1009_lt
  norm_num at hrat ⊢
  exact lt_of_le_of_lt hΛ hrat

theorem Lambda_bounds_1009 :
    (550653011272842963574907227315784759883099490122684597014105 : ℝ) / 10 ^ 60 <
      Lambda ∧
    Lambda <
      (550653011272842963579465933094387203471136467695308801315764 : ℝ) / 10 ^ 60 :=
  ⟨Lambda_gt_550653011272842963574907227315784759883099490122684597014105_div_1e60,
    Lambda_lt_550653011272842963579465933094387203471136467695308801315764_div_1e60⟩

theorem sandwichLowerRat_2003_2005_le_Lambda :
    (sandwichLowerRat 2003 2005 : ℝ) ≤ Lambda := by
  apply sandwichLowerRat_le_Lambda_of_tail_ge (N := 2003) (m := 2005) (by decide) (by norm_num)
  intro p hp_prime hp_gt
  have hp_ge_2004 : 2004 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge_2004 with hp2004 | hp2004
  · exact Nat.succ_le_of_lt hp2004
  · exfalso
    subst p
    exact (by decide : ¬ Nat.Prime 2004) hp_prime

set_option linter.style.nativeDecide false in
theorem primePhaseIntegralRat_2003_lt :
    primePhaseIntegralRat 2003 <
      (550653011272842963577971757142083257920591723109550420057790 : ℚ) / 10 ^ 60 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem sandwichLowerRat_2003_2005_gt :
    (550653011272842963577971756854046512125342959043141558898004 : ℚ) / 10 ^ 60 <
      sandwichLowerRat 2003 2005 := by
  native_decide

theorem Lambda_gt_550653011272842963577971756854046512125342959043141558898004_div_1e60 :
    (550653011272842963577971756854046512125342959043141558898004 : ℝ) / 10 ^ 60 <
      Lambda := by
  have hrat :
      ((550653011272842963577971756854046512125342959043141558898004 : ℚ) / 10 ^ 60 : ℝ) <
        (sandwichLowerRat 2003 2005 : ℝ) := by
    exact_mod_cast sandwichLowerRat_2003_2005_gt
  norm_num at hrat ⊢
  exact hrat.trans_le sandwichLowerRat_2003_2005_le_Lambda

theorem Lambda_lt_550653011272842963577971757142083257920591723109550420057790_div_1e60 :
    Lambda <
      (550653011272842963577971757142083257920591723109550420057790 : ℝ) / 10 ^ 60 := by
  have hΛ : Lambda ≤ phaseIntegral (primeSetUpTo 2003) :=
    Lambda_le_prime_truncation 2003
  rw [phaseIntegral_primeSetUpTo_eq_rat] at hΛ
  have hrat : (primePhaseIntegralRat 2003 : ℝ) <
      ((550653011272842963577971757142083257920591723109550420057790 : ℚ) / 10 ^ 60 : ℝ) := by
    exact_mod_cast primePhaseIntegralRat_2003_lt
  norm_num at hrat ⊢
  exact lt_of_le_of_lt hΛ hrat

theorem Lambda_bounds_2003 :
    (550653011272842963577971756854046512125342959043141558898004 : ℝ) / 10 ^ 60 <
      Lambda ∧
    Lambda <
      (550653011272842963577971757142083257920591723109550420057790 : ℝ) / 10 ^ 60 :=
  ⟨Lambda_gt_550653011272842963577971756854046512125342959043141558898004_div_1e60,
    Lambda_lt_550653011272842963577971757142083257920591723109550420057790_div_1e60⟩

end ProductInvariants.Certified
