import ProductInvariants.Finite.BernsteinProbe
import ProductInvariants.Prime.ErrorBounds
import ProductInvariants.Certified.PolynomialIntegral

/-!
# Phase I: the M = 16 partial tail-domination certificate

This file finishes the *partial* (variable upper limit `c ∈ (0,1]`) leg of the
tail-domination bypass.  The endpoint case `c = 1` is `Gap A`
(`phaseIntegral_gt_half_of_two_le`); here we upgrade it to every `c`.

The target is

  `block_partial_pos_of_two_le :
     0 < ∫ u in 0..c, (phaseProduct S u - (1 - u))`   for `c ∈ (0,1]`,

for every finite support `S` of integers `≥ 2`.  The chain is:

* `[A]` antitonicity: `phaseProduct (PM16 ∪ S) ≤ phaseProduct S` pointwise.
* `[B]` common-prefix error with the fixed prefix `R = {2,3}`:
  `phaseProduct PM16 - phaseProduct (PM16 ∪ S) ≤ ∑_{q ∈ tail} (1-u²)(1-u³)·uᵍ`.
* `[C]` telescope the `{2,3}`-weighted tail by the full geometric tail (step 1).
* `[D]+[E]` the Bernstein certificate (degree-134 cofactor `Q16`, certified
  positive once by `native_decide` in `BernsteinProbe.lean`) gives the strict
  partial inequality `∫₀ᶜ P[PM16] - ErrInf(c) > c − c²/2`.
-/

set_option linter.style.nativeDecide false
set_option maxRecDepth 8000

open MeasureTheory intervalIntegral

namespace ProductInvariants

open Polynomial

/-! ## The certified cofactor polynomial -/

/-- The degree-134 cofactor polynomial `Q16` realised over `ℚ`. -/
noncomputable def Q16poly : Polynomial ℚ := polyOfList Q16coeffs

/-- `Q16poly` is strictly positive throughout `[0,1]` (real points), inherited
from the once-and-for-all `native_decide` Bernstein certificate. -/
theorem Q16poly_pos_on_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 < (Q16poly).aeval x := by
  apply aeval_pos_of_myBernLo_pos Q16coeffs
  · native_decide
  · native_decide
  · exact Q16_bernLo_pos
  · exact hx

/-! ## Step-1 geometric telescope

For the `{2,3}`-prefix common-error bound we need the *step-1* telescope, i.e.
`(1 - u) · ∑ uᵐ⁺ᵏ ≤ uᵐ`, the `k+1`-indexed analogue of the step-2
`geometric_telescope_finite` already in `Certified/PolynomialIntegral.lean`. -/

theorem geometric_telescope_finite_step_one (m n : ℕ) (u : ℝ) :
    (1 - u) * ∑ k ∈ Finset.range n, u ^ (m + k) =
      u ^ m - u ^ (m + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have h1 : (1 - u) * u ^ (m + n) = u ^ (m + n) - u ^ (m + n) * u := by ring
      rw [h1, ← pow_succ]
      ring_nf

theorem telescope_sum_le_step_one (m : ℕ) (K : Finset ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u) * ∑ k ∈ K, u ^ (m + k) ≤ u ^ m := by
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
        ∑ k ∈ K, u ^ (m + k) ≤
          ∑ k ∈ Finset.range n, u ^ (m + k) :=
      Finset.sum_le_sum_of_subset_of_nonneg hK_sub
        (fun _ _ _ => pow_nonneg hu0 _)
    have h_telescope := geometric_telescope_finite_step_one m n u
    have h_1_sub_nonneg : 0 ≤ 1 - u := by linarith
    calc
      (1 - u) * ∑ k ∈ K, u ^ (m + k)
          ≤ (1 - u) * ∑ k ∈ Finset.range n, u ^ (m + k) :=
            mul_le_mul_of_nonneg_left h_sum_le h_1_sub_nonneg
      _ = u ^ m - u ^ (m + n) := h_telescope
      _ ≤ u ^ m := by linarith [pow_nonneg hu0 (m + n)]

/-- A finite set of exponents all `≥ m` telescopes (step 1) under `(1 - u)`. -/
theorem telescope_ge_sum_bound_from {m : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, m ≤ p)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u) * ∑ p ∈ S, u ^ p ≤ u ^ m := by
  let f : ℕ → ℕ := fun p => p - m
  have h_pow_eq : ∀ p ∈ S, u ^ p = u ^ (m + f p) := by
    intro p hp
    have hpm := hS p hp
    have : m + f p = p := by simp only [f]; omega
    rw [this]
  have h_f_inj : Set.InjOn f S := by
    intro p₁ hp₁ p₂ hp₂ hf_eq
    have h1 := hS p₁ hp₁
    have h2 := hS p₂ hp₂
    simp only [f] at hf_eq
    omega
  have h_sum_eq : ∑ p ∈ S, u ^ p = ∑ k ∈ S.image f, u ^ (m + k) := by
    conv_lhs => rw [Finset.sum_congr rfl h_pow_eq]
    show ∑ p ∈ S, u ^ (m + f p) = ∑ k ∈ S.image f, u ^ (m + k)
    rw [Finset.sum_image h_f_inj]
  rw [h_sum_eq]
  exact telescope_sum_le_step_one m (S.image f) u hu0 hu1

/-! ## Variable-limit integral of an `IPoly`

The existing `IPoly.integral_evalFrom` integrates over the fixed interval `[0,1]`.
For the partial certificate we need the *variable-limit* integral `∫₀ᶜ`, returned
as a real-valued antiderivative.  We define the real antiderivative
`IPoly.intTo p k c = ∑ aᵢ cᵏ⁺ⁱ⁺¹/(k+i+1)` and prove the FTC identity by
induction, mirroring the structure of `IPoly.integral_evalFrom`. -/

open Certified

/-- Real antiderivative-from-`0` value of `IPoly.evalFrom p k` at upper limit `c`. -/
noncomputable def IPoly.intTo : IPoly → ℕ → ℝ → ℝ
  | [], _k, _c => 0
  | a :: as, k, c => (a : ℝ) * c ^ (k + 1) / ((k : ℝ) + 1) + IPoly.intTo as (k + 1) c

theorem IPoly.integral_evalFrom_to (p : IPoly) (k : ℕ) (c : ℝ) :
    (∫ u in (0 : ℝ)..c, IPoly.evalFrom p k u) = IPoly.intTo p k c := by
  induction p generalizing k with
  | nil =>
      simp [IPoly.evalFrom, IPoly.intTo]
  | cons a as ih =>
      simp only [IPoly.evalFrom, IPoly.intTo]
      have hmono :
          (∫ u in (0 : ℝ)..c, (a : ℝ) * u ^ k) =
            (a : ℝ) * c ^ (k + 1) / ((k : ℝ) + 1) := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        rw [zero_pow (Nat.succ_ne_zero k), sub_zero]
        ring
      rw [intervalIntegral.integral_add]
      · rw [hmono, ih]
      · exact ((continuous_const.mul (continuous_id.pow k))).intervalIntegrable 0 c
      · exact (IPoly.continuous_evalFrom as (k + 1)).intervalIntegrable 0 c

/-- `intTo p k c` as an explicit finite sum over the coefficient list. -/
theorem IPoly.intTo_eq_sum (p : IPoly) (k : ℕ) (c : ℝ) :
    IPoly.intTo p k c =
      ∑ i ∈ Finset.range p.length,
        (p.getD i 0 : ℝ) * c ^ (k + i + 1) / ((k : ℝ) + i + 1) := by
  induction p generalizing k with
  | nil => simp [IPoly.intTo]
  | cons a as ih =>
      rw [IPoly.intTo, ih (k + 1)]
      -- RHS goal sum over range (a::as).length; peel the i=0 term.
      rw [List.length_cons, Finset.sum_range_succ']
      rw [List.getD_cons_zero]
      -- goal: a₀term + (ih sum) = (tail sum) + a₀term
      rw [add_comm]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [List.getD_cons_succ]
        have hexp : k + (i + 1) + 1 = k + 1 + i + 1 := by omega
        rw [hexp]
        push_cast
        ring_nf
      · simp

/-- Rational antiderivative coefficient list of an `IPoly`: coefficient of `c^0`
is `0`, and the coefficient of `c^(i+1)` is `aᵢ/(i+1)`. -/
def IPoly.antiderivQ (p : IPoly) : List ℚ :=
  0 :: (p.zipIdx.map (fun ai => (ai.1 : ℚ) / ((ai.2 : ℚ) + 1)))

theorem IPoly.antiderivQ_length (p : IPoly) :
    (IPoly.antiderivQ p).length = p.length + 1 := by
  simp [IPoly.antiderivQ]

theorem IPoly.antiderivQ_getD_succ (p : IPoly) (i : ℕ) (hi : i < p.length) :
    (IPoly.antiderivQ p).getD (i + 1) 0 = (p.getD i 0 : ℚ) / ((i : ℚ) + 1) := by
  unfold IPoly.antiderivQ
  rw [List.getD_cons_succ]
  have hlen : i < (p.zipIdx.map (fun ai => (ai.1 : ℚ) / ((ai.2 : ℚ) + 1))).length := by
    simpa using hi
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [List.getElem_map, List.getElem_zipIdx]
  rw [List.getD_eq_getElem _ _ hi]
  simp

/-- `aeval` of a `polyOfList` is the explicit coefficient sum. -/
theorem aeval_polyOfList_eq_sum (cs : List ℚ) (c : ℝ) :
    (polyOfList cs).aeval c =
      ∑ j ∈ Finset.range cs.length, (cs.getD j 0 : ℝ) * c ^ j := by
  unfold polyOfList
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Polynomial.aeval_monomial]
  simp

/-- The coefficient sum may be taken over any range at least as long as the list
(the extra terms vanish). -/
theorem aeval_polyOfList_eq_sum_range (cs : List ℚ) (c : ℝ) {n : ℕ}
    (hn : cs.length ≤ n) :
    (polyOfList cs).aeval c =
      ∑ j ∈ Finset.range n, (cs.getD j 0 : ℝ) * c ^ j := by
  rw [aeval_polyOfList_eq_sum]
  rw [← Finset.sum_range_add_sum_Ico _ hn]
  have hzero : ∑ j ∈ Finset.Ico cs.length n, (cs.getD j 0 : ℝ) * c ^ j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [List.getD_eq_default cs 0 (by simpa using (Finset.mem_Ico.mp hj).1)]
    simp
  rw [hzero, add_zero]

/-- The real antiderivative `intTo p 0 c` equals the `aeval` of the rational
antiderivative polynomial. -/
theorem IPoly.intTo_eq_aeval (p : IPoly) (c : ℝ) :
    IPoly.intTo p 0 c = (polyOfList (IPoly.antiderivQ p)).aeval c := by
  rw [IPoly.intTo_eq_sum]
  rw [aeval_polyOfList_eq_sum]
  -- LHS: ∑_{i<p.length} aᵢ c^(i+1)/(i+1)
  -- RHS: ∑_{j<antiderivQ.length} (antiderivQ[j]:ℝ) c^j
  --      = (j=0 term 0) + ∑_{i<p.length} (aᵢ/(i+1):ℝ) c^(i+1)
  rw [IPoly.antiderivQ_length, Finset.sum_range_succ']
  have h0 : ((IPoly.antiderivQ p).getD 0 0 : ℝ) * c ^ 0 = 0 := by
    simp [IPoly.antiderivQ]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [IPoly.antiderivQ_getD_succ p i (Finset.mem_range.mp hi)]
  push_cast
  rw [Nat.zero_add]
  ring

/-! ## The M = 16 partial certificate -/

/-- The fixed degree-16 prefix support `{2,3,…,16}`. -/
def PM16 : Finset ℕ := Finset.Icc 2 16

/-- `PM16` as a sorted factor list `[2,3,…,16]`. -/
def PM16factors : List ℕ := PM16.sort (· ≤ ·)

/-- The integer-polynomial prefix `∏_{n=2}^{16}(1 - Xⁿ)`. -/
def P16IPoly : IPoly := IPoly.ofFactors PM16factors

theorem P16IPoly_eval (u : ℝ) :
    IPoly.evalFrom P16IPoly 0 u = phaseProduct PM16 u := by
  unfold P16IPoly PM16factors
  rw [IPoly.evalFrom_ofFactors]
  have hperm :
      @List.Perm ℝ
        ((PM16.sort (· ≤ ·)).map (fun n => (1 - u ^ n)))
        (PM16.toList.map (fun n => (1 - u ^ n))) :=
    (Finset.sort_perm_toList PM16 (· ≤ ·)).map _
  rw [hperm.prod_eq]
  simp [phaseProduct]

/-- The variable-limit integral of the prefix as a rational-polynomial `aeval`. -/
noncomputable def intP16poly : Polynomial ℚ := polyOfList (IPoly.antiderivQ P16IPoly)

theorem integral_phaseProduct_PM16 (c : ℝ) :
    (∫ u in (0 : ℝ)..c, phaseProduct PM16 u) = (intP16poly).aeval c := by
  have hcongr :
      (∫ u in (0 : ℝ)..c, phaseProduct PM16 u) =
        ∫ u in (0 : ℝ)..c, IPoly.evalFrom P16IPoly 0 u := by
    apply intervalIntegral.integral_congr
    intro u _hu
    exact (P16IPoly_eval u).symm
  rw [hcongr, IPoly.integral_evalFrom_to, IPoly.intTo_eq_aeval]
  rfl

/-! ## The certificate factorisation `C16 = c² · Q16`

The certificate value is
`C16(c) = ∫₀ᶜ P[PM16] − ErrInf₁₆(c) − (c − c²/2)`, which factors as `c²·Q16(c)`.
All algebra is done as a single `List ℚ` identity (`native_decide`), never as a
degree-136 real expression. -/

/-- Coefficient list of `ErrInf₁₆ + (c − c²/2)` (subtracted terms), as a
`List ℚ` (index = power of `c`):
`c − c²/2 + c¹⁸/18 + c¹⁹/19 − c²¹/21 − c²²/22`. -/
def sub16coeffs : List ℚ :=
  [(0 : ℚ), (1 : ℚ), (-1/2 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
   (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
   (0 : ℚ), (0 : ℚ), (1/18 : ℚ), (1/19 : ℚ), (0 : ℚ), (-1/21 : ℚ), (-1/22 : ℚ)]

/-- Pointwise ℚ-list subtraction (truncating to the shorter, padding with 0). -/
def listSubQ : List ℚ → List ℚ → List ℚ
  | [], q => q.map (fun x => -x)
  | p, [] => p
  | a :: as, b :: bs => (a - b) :: listSubQ as bs

theorem listSubQ_getD (p q : List ℚ) (i : ℕ) :
    (listSubQ p q).getD i 0 = p.getD i 0 - q.getD i 0 := by
  induction p generalizing q i with
  | nil =>
      simp only [listSubQ, List.getD_nil, zero_sub]
      induction q generalizing i with
      | nil => simp [List.getD]
      | cons b bs ihq =>
          cases i with
          | zero => simp [List.getD]
          | succ n =>
              simp only [List.map_cons, List.getD_cons_succ]
              exact ihq n
  | cons a as ih =>
      cases q with
      | nil => simp [listSubQ, List.getD]
      | cons b bs =>
          cases i with
          | zero => simp [listSubQ, List.getD]
          | succ n => simp only [listSubQ, List.getD_cons_succ]; exact ih bs n

theorem listSubQ_length (p q : List ℚ) :
    (listSubQ p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => cases q <;> simp [listSubQ]
  | cons a as ih =>
      cases q with
      | nil => simp [listSubQ]
      | cons b bs => simp [listSubQ, ih bs, Nat.succ_max_succ]

/-- `aeval` distributes over `listSubQ`. -/
theorem aeval_polyOfList_listSubQ (p q : List ℚ) (c : ℝ) :
    (polyOfList (listSubQ p q)).aeval c =
      (polyOfList p).aeval c - (polyOfList q).aeval c := by
  set n := max (listSubQ p q).length (max p.length q.length) with hn
  have h1 : (listSubQ p q).length ≤ n := le_max_left _ _
  have h2 : p.length ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
  have h3 : q.length ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  rw [aeval_polyOfList_eq_sum_range (listSubQ p q) c h1,
      aeval_polyOfList_eq_sum_range p c h2,
      aeval_polyOfList_eq_sum_range q c h3]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [listSubQ_getD]
  push_cast
  ring

/-- The full certificate coefficient list `C16 = intP16 − sub16`. -/
def C16coeffs : List ℚ :=
  listSubQ (IPoly.antiderivQ P16IPoly) sub16coeffs

/-- **The list-level factorisation** `C16 = X² · Q16`, i.e. the coefficient list
of `C16` is `Q16coeffs` shifted up by two (prepending two zeros).  This is the
single exact rational identity that powers the certificate; checked by
`native_decide`. -/
theorem C16coeffs_eq : C16coeffs = (0 : ℚ) :: (0 : ℚ) :: Q16coeffs := by
  native_decide

/-- `aeval` of a two-zero-prepended list is `c²` times the `aeval` of the base. -/
theorem aeval_cons_two_zero (cs : List ℚ) (c : ℝ) :
    (polyOfList ((0 : ℚ) :: (0 : ℚ) :: cs)).aeval c =
      c ^ 2 * (polyOfList cs).aeval c := by
  rw [aeval_polyOfList_eq_sum, aeval_polyOfList_eq_sum]
  rw [List.length_cons, List.length_cons]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  -- peel the two leading (zero) terms
  simp only [List.getD_cons_zero, List.getD_cons_succ, Rat.cast_zero, zero_mul,
    add_zero, pow_zero, mul_one]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hexp : i + 1 + 1 = 2 + i := by omega
  rw [hexp, pow_add]
  ring

/-- The subtracted-terms polynomial evaluates to `c − c²/2 + ErrInf₁₆(c)`. -/
theorem aeval_sub16coeffs (c : ℝ) :
    (polyOfList sub16coeffs).aeval c =
      c - c ^ 2 / 2 + c ^ 18 / 18 + c ^ 19 / 19 - c ^ 21 / 21 - c ^ 22 / 22 := by
  rw [aeval_polyOfList_eq_sum]
  have hlen : sub16coeffs.length = 23 := by decide
  rw [hlen]
  -- expand the 23-term sum; all but six coefficients are zero
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub16coeffs,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  ring

/-- The inhomogeneous "tail-error + linear" correction `ErrInf₁₆(c) = c¹⁸/18 +
c¹⁹/19 − c²¹/21 − c²²/22`. -/
noncomputable def errInf16 (c : ℝ) : ℝ :=
  c ^ 18 / 18 + c ^ 19 / 19 - c ^ 21 / 21 - c ^ 22 / 22

/-- **The certificate factorisation.**

`∫₀ᶜ P[PM16] − ErrInf₁₆(c) − (c − c²/2) = c² · Q16(c)`. -/
theorem C16_factor (c : ℝ) :
    (∫ u in (0 : ℝ)..c, phaseProduct PM16 u) - errInf16 c - (c - c ^ 2 / 2) =
      c ^ 2 * (Q16poly).aeval c := by
  rw [integral_phaseProduct_PM16]
  -- intP16poly.aeval c = (polyOfList C16coeffs).aeval c + (polyOfList sub16coeffs).aeval c
  have hC : (polyOfList C16coeffs).aeval c =
      intP16poly.aeval c - (polyOfList sub16coeffs).aeval c := by
    unfold C16coeffs intP16poly
    rw [aeval_polyOfList_listSubQ]
  have hsplit : intP16poly.aeval c =
      (polyOfList C16coeffs).aeval c + (polyOfList sub16coeffs).aeval c := by
    rw [hC]; ring
  rw [hsplit, aeval_sub16coeffs]
  rw [C16coeffs_eq, aeval_cons_two_zero]
  unfold errInf16 Q16poly
  ring

/-- **The M=16 partial certificate (strict).**

For every `c ∈ (0,1]`,
`∫₀ᶜ P[PM16] − ErrInf₁₆(c) > c − c²/2`.

This is the certified `[D]+[E]` step: the certificate `C16(c) = c²·Q16(c)` is
strictly positive because `c² > 0` and `Q16(c) > 0` (Bernstein certificate). -/
theorem tailCert16_pos {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    c - c ^ 2 / 2 < (∫ u in (0 : ℝ)..c, phaseProduct PM16 u) - errInf16 c := by
  have hfac := C16_factor c
  have hQpos : 0 < (Q16poly).aeval c :=
    Q16poly_pos_on_Icc ⟨hc0.le, hc1⟩
  have hcsq : 0 < c ^ 2 := by positivity
  have hpos : 0 < c ^ 2 * (Q16poly).aeval c := mul_pos hcsq hQpos
  -- C16(c) = (∫ − ErrInf) − (c − c²/2) = c²·Q16(c) > 0
  linarith [hfac]

/-! ## The pointwise PM16-union-tail error bound -/

/-- `phaseProduct {2,3} u = (1-u²)(1-u³)`. -/
theorem phaseProduct_two_three (u : ℝ) :
    phaseProduct {2, 3} u = (1 - u ^ 2) * (1 - u ^ 3) := by
  unfold phaseProduct
  rw [Finset.prod_pair (by norm_num)]

/-- **Pointwise tail-error bound `[B]+[C]`.**

If `PM16 ⊆ T` and every extra exponent `q ∈ T \ PM16` is `≥ 17`, then for
`u ∈ [0,1]`,

  `P[PM16] u − P[T] u ≤ u¹⁷ + u¹⁸ − u²⁰ − u²¹`.

Proof: `common_prefix_error_pointwise` with prefix `R = {2,3}` gives the bound
`(1-u²)(1-u³)·∑_{q∈T\PM16} uᵍ`.  Factoring `(1-u²) = (1-u)(1+u)` and applying the
step-1 telescope (`telescope_ge_sum_bound_from`, `m = 17`) replaces the tail sum
by `u¹⁷`, leaving `(1+u)(1-u³)u¹⁷ = u¹⁷ + u¹⁸ − u²⁰ − u²¹`. -/
theorem tailErr16_pointwise {T : Finset ℕ} (hPT : PM16 ⊆ T)
    (hK17 : ∀ q ∈ T \ PM16, 17 ≤ q) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    phaseProduct PM16 u - phaseProduct T u ≤
      u ^ 17 + u ^ 18 - u ^ 20 - u ^ 21 := by
  obtain ⟨hu0, hu1⟩ := hu
  -- Step [B]: common-prefix error with R = {2,3}.
  have hRS : ({2, 3} : Finset ℕ) ⊆ PM16 := by
    intro n hn
    fin_cases hn <;> (unfold PM16; decide)
  have hB := common_prefix_error_pointwise hRS hPT ⟨hu0, hu1⟩
  -- Rewrite the RHS of [B] as (1-u²)(1-u³)·∑ uᵍ.
  have hBsum :
      ∑ q ∈ T \ PM16, phaseProduct {2, 3} u * u ^ q =
        (1 - u ^ 2) * (1 - u ^ 3) * ∑ q ∈ T \ PM16, u ^ q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [phaseProduct_two_three]
  rw [hBsum] at hB
  -- Step [C]: telescope ∑_{q≥17} uᵍ ≤ u¹⁷/(1-u), i.e. (1-u)∑ ≤ u¹⁷.
  have hTel := telescope_ge_sum_bound_from (T \ PM16) hK17 u hu0 hu1
  -- (1-u²)(1-u³) = (1+u)(1-u³)·(1-u);  (1+u)(1-u³) ≥ 0.
  have hfac_nonneg : 0 ≤ (1 + u) * (1 - u ^ 3) := by
    have h1 : 0 ≤ 1 + u := by linarith
    have h2 : 0 ≤ 1 - u ^ 3 := one_sub_pow_nonneg_of_mem_Icc ⟨hu0, hu1⟩ 3
    positivity
  have hsum_nonneg : 0 ≤ ∑ q ∈ T \ PM16, u ^ q :=
    Finset.sum_nonneg (fun q _ => pow_nonneg hu0 q)
  -- Chain: (1-u²)(1-u³)·∑ = (1+u)(1-u³)·[(1-u)·∑] ≤ (1+u)(1-u³)·u¹⁷.
  have hchain :
      (1 - u ^ 2) * (1 - u ^ 3) * ∑ q ∈ T \ PM16, u ^ q ≤
        (1 + u) * (1 - u ^ 3) * u ^ 17 := by
    have hrw :
        (1 - u ^ 2) * (1 - u ^ 3) * ∑ q ∈ T \ PM16, u ^ q =
          (1 + u) * (1 - u ^ 3) * ((1 - u) * ∑ q ∈ T \ PM16, u ^ q) := by
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hTel hfac_nonneg
  -- (1+u)(1-u³)u¹⁷ = u¹⁷ + u¹⁸ − u²⁰ − u²¹.
  have hexpand :
      (1 + u) * (1 - u ^ 3) * u ^ 17 = u ^ 17 + u ^ 18 - u ^ 20 - u ^ 21 := by
    ring
  rw [hexpand] at hchain
  exact le_trans hB hchain

/-! ## The integrated partial tail bound -/

/-- `∫₀ᶜ (u¹⁷ + u¹⁸ − u²⁰ − u²¹) du = errInf16 c`. -/
theorem integral_errInf16 (c : ℝ) :
    (∫ u in (0 : ℝ)..c, (u ^ 17 + u ^ 18 - u ^ 20 - u ^ 21)) = errInf16 c := by
  have h17 : IntervalIntegrable (fun u : ℝ => u ^ 17) volume 0 c :=
    (continuous_id.pow 17).intervalIntegrable 0 c
  have h18 : IntervalIntegrable (fun u : ℝ => u ^ 18) volume 0 c :=
    (continuous_id.pow 18).intervalIntegrable 0 c
  have h20 : IntervalIntegrable (fun u : ℝ => u ^ 20) volume 0 c :=
    (continuous_id.pow 20).intervalIntegrable 0 c
  have h21 : IntervalIntegrable (fun u : ℝ => u ^ 21) volume 0 c :=
    (continuous_id.pow 21).intervalIntegrable 0 c
  rw [intervalIntegral.integral_sub ((h17.add h18).sub h20) h21,
      intervalIntegral.integral_sub (h17.add h18) h20,
      intervalIntegral.integral_add h17 h18,
      integral_pow, integral_pow, integral_pow, integral_pow]
  unfold errInf16
  norm_num

/-- **Integrated partial tail bound `[A]+[B]+[C]`.**

If `PM16 ⊆ T`, every extra exponent is `≥ 17`, and `0 ≤ c ≤ 1`, then

  `∫₀ᶜ P[PM16] − ∫₀ᶜ P[T] ≤ ErrInf₁₆(c)`.

Proof: integrate the pointwise bound `tailErr16_pointwise` over `[0,c]`. -/
theorem tailErr16_partial {T : Finset ℕ} (hPT : PM16 ⊆ T)
    (hK17 : ∀ q ∈ T \ PM16, 17 ≤ q) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ u in (0 : ℝ)..c, phaseProduct PM16 u) -
        (∫ u in (0 : ℝ)..c, phaseProduct T u) ≤ errInf16 c := by
  have hintP : IntervalIntegrable (fun u : ℝ => phaseProduct PM16 u) volume 0 c :=
    (continuous_phaseProduct PM16).intervalIntegrable 0 c
  have hintT : IntervalIntegrable (fun u : ℝ => phaseProduct T u) volume 0 c :=
    (continuous_phaseProduct T).intervalIntegrable 0 c
  have hintE :
      IntervalIntegrable (fun u : ℝ => u ^ 17 + u ^ 18 - u ^ 20 - u ^ 21) volume 0 c :=
    ((((continuous_id.pow 17).add (continuous_id.pow 18)).sub
      (continuous_id.pow 20)).sub (continuous_id.pow 21)).intervalIntegrable 0 c
  -- ∫(P[PM16] − P[T]) ≤ ∫(u¹⁷+u¹⁸−u²⁰−u²¹) pointwise on [0,c] ⊆ [0,1].
  have hmono :
      (∫ u in (0 : ℝ)..c, (phaseProduct PM16 u - phaseProduct T u)) ≤
        ∫ u in (0 : ℝ)..c, (u ^ 17 + u ^ 18 - u ^ 20 - u ^ 21) := by
    apply intervalIntegral.integral_mono_on hc0 (hintP.sub hintT) hintE
    intro u hu
    obtain ⟨hu0, huc⟩ := hu
    exact tailErr16_pointwise hPT hK17 ⟨hu0, le_trans huc hc1⟩
  rw [intervalIntegral.integral_sub hintP hintT] at hmono
  rw [integral_errInf16] at hmono
  exact hmono

/-! ## The assembled block partial positivity -/

/-- `∫₀ᶜ (1 − u) du = c − c²/2`. -/
theorem integral_one_sub (c : ℝ) :
    (∫ u in (0 : ℝ)..c, (1 - u)) = c - c ^ 2 / 2 := by
  have h1 : IntervalIntegrable (fun _u : ℝ => (1 : ℝ)) volume 0 c :=
    continuous_const.intervalIntegrable 0 c
  have hid : IntervalIntegrable (fun u : ℝ => u) volume 0 c :=
    continuous_id.intervalIntegrable 0 c
  rw [intervalIntegral.integral_sub h1 hid]
  simp [integral_id]

/-- **Block partial positivity (`c ∈ (0,1]`).**

For every finite support `S` of integers `≥ 2` and every `c ∈ (0,1]`,

  `0 < ∫₀ᶜ (P[S] u − (1 − u)) du`.

This is the variable-upper-limit refinement of Gap A.  The proof chains
`[A]` antitonicity, `[B]+[C]` the integrated tail bound `tailErr16_partial`, and
`[D]+[E]` the Bernstein certificate `tailCert16_pos`, against the closed form
`∫₀ᶜ (1−u) = c − c²/2`. -/
theorem block_partial_pos_of_two_le {S : Finset ℕ} (hS : ∀ n ∈ S, 2 ≤ n)
    {c : ℝ} (hc : c ∈ Set.Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..c, (phaseProduct S u - (1 - u)) := by
  obtain ⟨hc0, hc1⟩ := hc
  classical
  set T : Finset ℕ := PM16 ∪ S with hT
  -- PM16 ⊆ T and S ⊆ T.
  have hPT : PM16 ⊆ T := Finset.subset_union_left
  have hST : S ⊆ T := Finset.subset_union_right
  -- Every extra exponent q ∈ T \ PM16 lies in S and is ≥ 17.
  have hK17 : ∀ q ∈ T \ PM16, 17 ≤ q := by
    intro q hq
    rw [Finset.mem_sdiff] at hq
    obtain ⟨hqT, hqP⟩ := hq
    have hqS : q ∈ S := by
      rw [hT, Finset.mem_union] at hqT
      exact hqT.resolve_left hqP
    have hq2 : 2 ≤ q := hS q hqS
    have : q ∉ Finset.Icc 2 16 := by simpa [PM16] using hqP
    rw [Finset.mem_Icc] at this
    omega
  -- [A] antitonicity, integrated: ∫P[T] ≤ ∫P[S].
  have hintS : IntervalIntegrable (fun u : ℝ => phaseProduct S u) volume 0 c :=
    (continuous_phaseProduct S).intervalIntegrable 0 c
  have hintT : IntervalIntegrable (fun u : ℝ => phaseProduct T u) volume 0 c :=
    (continuous_phaseProduct T).intervalIntegrable 0 c
  have hA : (∫ u in (0 : ℝ)..c, phaseProduct T u) ≤
      ∫ u in (0 : ℝ)..c, phaseProduct S u := by
    apply intervalIntegral.integral_mono_on hc0.le hintT hintS
    intro u hu
    obtain ⟨hu0, huc⟩ := hu
    exact phaseProduct_antitone hST ⟨hu0, le_trans huc hc1⟩
  -- [B]+[C]: ∫P[PM16] − ∫P[T] ≤ errInf16 c.
  have hBC := tailErr16_partial hPT hK17 hc0.le hc1
  -- [D]+[E]: c − c²/2 < ∫P[PM16] − errInf16 c.
  have hDE := tailCert16_pos hc0 hc1
  -- ∫(P[S] − (1−u)) = ∫P[S] − (c − c²/2).
  have hint1 : IntervalIntegrable (fun u : ℝ => (1 : ℝ) - u) volume 0 c :=
    (continuous_const.sub continuous_id).intervalIntegrable 0 c
  rw [intervalIntegral.integral_sub hintS hint1, integral_one_sub]
  -- Chain everything.
  linarith

end ProductInvariants
