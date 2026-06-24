import LeanCert

/-!
# List-based Bernstein positivity bridge

`Polynomial ℚ` is noncomputable, so we cannot `native_decide` the leancert
`boundPolyBernstein` interval directly.  This file builds the bridge:

1. `polyOfList cs : Polynomial ℚ` — a polynomial with `coeff i = cs.getD i 0`.
2. The leancert Bernstein lower bound on `[0,1]` (center `0`) equals a fully
   computable list function `bernLoList cs`, which `native_decide` can evaluate.
3. Hence positivity of `bernLoList cs` (checked by `native_decide`) yields
   `0 < aeval x (polyOfList cs)` for all `x ∈ [0,1]`.
-/

set_option linter.style.nativeDecide false

open LeanCert.Core LeanCert.Engine Polynomial

namespace ProductInvariants

/-- Polynomial with coefficient list `cs` (index = power of `X`). -/
noncomputable def polyOfList (cs : List ℚ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range cs.length, Polynomial.monomial i (cs.getD i 0)

theorem polyOfList_coeff (cs : List ℚ) (i : ℕ) :
    (polyOfList cs).coeff i = cs.getD i 0 := by
  unfold polyOfList
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hi : i < cs.length
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg hb]
    · intro h; exact absurd (Finset.mem_range.mpr hi) h
  · rw [List.getD_eq_default _ _ (by omega)]
    apply Finset.sum_eq_zero
    intro b hb
    have : b ≠ i := by rintro rfl; exact hi (Finset.mem_range.mp hb)
    rw [if_neg this]

/-- With `α = 0, β = 1`, `transformPolyCoeffs` reads off the coefficients
directly: the `0^(i-j)` factor kills every term except `i = j`. -/
theorem transformPolyCoeffs_zero_one (p : Polynomial ℚ) :
    transformPolyCoeffs p 0 1 =
      List.ofFn (fun j : Fin (p.natDegree + 1) => p.coeff j.val) := by
  unfold transformPolyCoeffs
  simp only [sub_zero]
  congr 1
  funext j
  -- sum over k of p.coeff (j+k) * binom(j+k,j) * 0^(j+k-j) * 1^j
  -- = (k=0 term) since 0^(positive) = 0
  rw [Finset.sum_eq_single 0]
  · simp [binomialRat]
  · intro k _ hk
    have : (0 : ℚ) ^ (j.val + k - j.val) = 0 := by
      rw [show j.val + k - j.val = k by omega]
      exact zero_pow hk
    rw [this]; ring
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- `polyOfList cs` has degree `< cs.length`. -/
theorem polyOfList_natDegree_lt (cs : List ℚ) (hcs : cs ≠ []) :
    (polyOfList cs).natDegree < cs.length := by
  unfold polyOfList
  apply lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _)
  simp only [Function.comp]
  rw [Finset.fold_max_lt]
  refine ⟨by simpa using List.length_pos_of_ne_nil hcs, ?_⟩
  intro i hi
  exact lt_of_le_of_lt (Polynomial.natDegree_monomial_le _) (Finset.mem_range.mp hi)

/-- If the last coefficient is nonzero, the degree is exactly `length - 1`. -/
theorem polyOfList_natDegree (cs : List ℚ) (hcs : cs ≠ [])
    (hlast : cs.getD (cs.length - 1) 0 ≠ 0) :
    (polyOfList cs).natDegree = cs.length - 1 := by
  have hlen : 0 < cs.length := List.length_pos_of_ne_nil hcs
  apply le_antisymm
  · have := polyOfList_natDegree_lt cs hcs; omega
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [polyOfList_coeff]
    exact hlast

/-- Computable Bernstein coefficient list for `polyOfList cs` on `[0,1]`,
center `0`.  Requires `cs.getLast ≠ 0` so the polynomial degree matches
`cs.length - 1`. -/
def myBernCoeffs (cs : List ℚ) : List ℚ :=
  monomialToBernstein (List.ofFn (fun j : Fin cs.length => cs.getD j 0))

/-- The leancert Bernstein coefficient list equals our computable list, when the
leading coefficient is nonzero. -/
theorem bernsteinCoeffsForDomain_eq (cs : List ℚ) (hcs : cs ≠ [])
    (hlast : cs.getD (cs.length - 1) 0 ≠ 0) :
    bernsteinCoeffsForDomain (polyOfList cs) 0 1 0 = myBernCoeffs cs := by
  have hdeg := polyOfList_natDegree cs hcs hlast
  have hlen : 0 < cs.length := List.length_pos_of_ne_nil hcs
  unfold bernsteinCoeffsForDomain myBernCoeffs
  simp only [sub_zero]
  congr 1
  rw [transformPolyCoeffs_zero_one]
  -- both are List.ofFn over Fin (natDegree+1) resp Fin cs.length; lengths agree
  have heq : (polyOfList cs).natDegree + 1 = cs.length := by omega
  -- rewrite the Fin index set
  apply List.ext_getElem
  · simp [heq]
  · intro n h1 h2
    simp only [List.getElem_ofFn]
    rw [polyOfList_coeff]

/-- Computable Bernstein lower bound for `polyOfList cs` on `[0,1]`. -/
def myBernLo (cs : List ℚ) : ℚ :=
  match myBernCoeffs cs with
  | [] => 0
  | x :: xs => (listMinMax (x :: xs) x).1

/-- The leancert Bernstein interval lower endpoint equals our computable
`myBernLo`. -/
theorem boundPolyBernstein_lo_eq (cs : List ℚ) (hcs : cs ≠ [])
    (hlast : cs.getD (cs.length - 1) 0 ≠ 0) :
    (boundPolyBernstein (polyOfList cs) ⟨0, 1, by norm_num⟩ 0).lo = myBernLo cs := by
  unfold boundPolyBernstein myBernLo
  rw [show (⟨0, 1, by norm_num⟩ : IntervalRat).lo = 0 from rfl,
      show (⟨0, 1, by norm_num⟩ : IntervalRat).hi = 1 from rfl,
      bernsteinCoeffsForDomain_eq cs hcs hlast]
  -- myBernCoeffs cs is nonempty: monomialToBernstein is a List.ofFn over Fin (_+1)
  have hne : myBernCoeffs cs ≠ [] := by
    have hlen : (myBernCoeffs cs).length = (cs.length - 1) + 1 := by
      unfold myBernCoeffs monomialToBernstein
      simp [List.length_ofFn]
    rw [← List.length_pos_iff_ne_nil, hlen]; omega
  cases h : myBernCoeffs cs with
  | nil => exact absurd h hne
  | cons x xs => rfl

/-- **Bernstein positivity bridge.**  If the computable Bernstein lower bound of
`polyOfList cs` on `[0,1]` is positive (checkable by `native_decide`), then the
polynomial is positive throughout `[0,1]`. -/
theorem aeval_pos_of_myBernLo_pos (cs : List ℚ) (hcs : cs ≠ [])
    (hlast : cs.getD (cs.length - 1) 0 ≠ 0) (hpos : 0 < myBernLo cs)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 < (polyOfList cs).aeval x := by
  have hmem : x ∈ (⟨0, 1, by norm_num⟩ : IntervalRat) := by
    simp only [IntervalRat.mem_def]
    exact_mod_cast hx
  have hbound := poly_eval_mem_boundPolyBernstein (polyOfList cs) ⟨0, 1, by norm_num⟩ 0 x hmem
  simp only [IntervalRat.mem_def, Rat.cast_zero, sub_zero] at hbound
  have hlo : (0 : ℝ) < ((boundPolyBernstein (polyOfList cs) ⟨0, 1, by norm_num⟩ 0).lo : ℝ) := by
    rw [boundPolyBernstein_lo_eq cs hcs hlast]
    exact_mod_cast hpos
  exact lt_of_lt_of_le hlo hbound.1

end ProductInvariants
