import ProductInvariants.Finite.Integral

/-!
# The single-multiple prime-exchange step (`k = 1`)

This file formalises the **elementary, fully rigorous** kernel of the prime
exchange lemma: replacing one exponent `m` in an exponent set by a smaller
exponent `p ≤ m` (keeping the rest fixed) cannot increase the phase integral
`F`.

The deep `k ≥ 2` exchange lemma — where several multiples `m₁,…,m_k` of a prime
`p` are simultaneously replaced by `p` — reduces to a delicate integrated
positivity statement (`∫₀¹ Q(u)[∏(1-u^{mᵢ}) - (1-u^p)] du > 0`) whose integrand
is **not** pointwise signed. That lemma is *not* proved here; it is the genuine
analytic crux and currently lacks a paper proof.

By contrast the `k = 1` case is pointwise:
`(1 - u^p) ≤ (1 - u^m)` on `[0,1]` whenever `p ≤ m`, since `u ↦ u^n` is
antitone in `n` on `[0,1]`. The divisibility structure of the exchange
(`m = t·p`) enters *only* to supply `p ≤ m`.
-/

open MeasureTheory intervalIntegral

namespace ProductInvariants

/-- On `[0,1]` the map `n ↦ 1 - u^n` is monotone in the exponent:
a smaller exponent yields a smaller value. -/
theorem one_sub_pow_le_one_sub_pow_of_le {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) {p m : ℕ} (hpm : p ≤ m) :
    1 - u ^ p ≤ 1 - u ^ m := by
  have hpow : u ^ m ≤ u ^ p := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpm
    rw [pow_add]
    calc u ^ p * u ^ k ≤ u ^ p * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hu.1 hu.2) (pow_nonneg hu.1 p)
      _ = u ^ p := mul_one _
  linarith

/-- Inserting a fresh exponent factors the phase product. -/
theorem phaseProduct_insert {S : Finset ℕ} {n : ℕ} (hn : n ∉ S) (u : ℝ) :
    phaseProduct (insert n S) u = (1 - u ^ n) * phaseProduct S u := by
  unfold phaseProduct
  rw [Finset.prod_insert hn]

/--
**Single-exponent replacement is monotone.**

If `p` and `m` are both absent from `S` and `p ≤ m`, then replacing `m` by the
smaller exponent `p` does not increase the phase integral:
`F(S ∪ {p}) ≤ F(S ∪ {m})`.
-/
theorem phaseIntegral_replace_le {S : Finset ℕ} {p m : ℕ}
    (hp : p ∉ S) (hm : m ∉ S) (hpm : p ≤ m) :
    phaseIntegral (insert p S) ≤ phaseIntegral (insert m S) := by
  unfold phaseIntegral
  refine intervalIntegral.integral_mono_on (by norm_num)
    (intervalIntegrable_phaseProduct _) (intervalIntegrable_phaseProduct _) ?_
  intro u hu
  rw [phaseProduct_insert hp, phaseProduct_insert hm]
  exact mul_le_mul_of_nonneg_right
    (one_sub_pow_le_one_sub_pow_of_le hu hpm)
    (phaseProduct_nonneg_on_Icc S hu)

/--
**The `k = 1` prime-exchange lemma.**

Let `p ≥ 1` and let `m = t·p` be a single multiple of `p` (with `t ≥ 1`, so
`m ≥ p`). If neither `p` nor `m` already lies in the remaining set `S`, then
swapping the multiple `m` out for `p` does not increase `F`:

`F(S ∪ {p}) ≤ F(S ∪ {t·p})`.

This is exactly the descent step `F(A') ≤ F(A)` for `A = S ∪ {t·p}`,
`A' = S ∪ {p}`, in the special case where `p` has a *single* multiple in the
antichain.
-/
theorem phaseIntegral_exchange_multiple_le {S : Finset ℕ} {p t : ℕ}
    (hp : p ∉ S) (hm : t * p ∉ S) (ht : 1 ≤ t) :
    phaseIntegral (insert p S) ≤ phaseIntegral (insert (t * p) S) := by
  have hpm : p ≤ t * p := by
    calc p = 1 * p := (one_mul p).symm
      _ ≤ t * p := Nat.mul_le_mul_right p ht
  exact phaseIntegral_replace_le hp hm hpm

/-! ## Strict version

The replacement is *strictly* decreasing once `p < m`, provided the remaining
exponents are genuine (`≥ 1`) so the leftover product `P[S]` does not vanish on
`(0,1)`. We exhibit `u = 1/2` as an explicit witness where the two integrands
differ strictly.
-/

/-- On the open interval `(0,1)` every factor `1 - u^n` is strictly positive
when `n ≥ 1`. -/
theorem one_sub_pow_pos_of_mem_Ioo {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (hn : 1 ≤ n) : 0 < 1 - u ^ n := by
  have hlt : u ^ n < 1 := pow_lt_one₀ hu.1.le hu.2 (Nat.one_le_iff_ne_zero.mp hn)
  linarith

/-- If every exponent in `S` is at least `1`, the phase product is strictly
positive on the open interval `(0,1)`. -/
theorem phaseProduct_pos_of_mem_Ioo {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 < phaseProduct S u := by
  unfold phaseProduct
  exact Finset.prod_pos (fun n hn => one_sub_pow_pos_of_mem_Ioo hu (hS n hn))

/-- On `(0,1)` a strictly smaller exponent gives a strictly smaller value:
`1 - u^p < 1 - u^m` when `p < m`. -/
theorem one_sub_pow_lt_one_sub_pow_of_lt {u : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) {p m : ℕ} (hpm : p < m) :
    1 - u ^ p < 1 - u ^ m := by
  have hpow : u ^ m < u ^ p :=
    (pow_lt_pow_iff_right_of_lt_one₀ hu.1 hu.2).mpr hpm
  linarith

/--
**Single-exponent replacement is strictly monotone.**

If `p` and `m` are absent from `S`, `p < m`, and every remaining exponent is
`≥ 1`, then replacing `m` by the strictly smaller exponent `p` *strictly*
decreases the phase integral: `F(S ∪ {p}) < F(S ∪ {m})`.
-/
theorem phaseIntegral_replace_lt {S : Finset ℕ} {p m : ℕ}
    (hp : p ∉ S) (hm : m ∉ S) (hpm : p < m) (hS : ∀ n ∈ S, 1 ≤ n) :
    phaseIntegral (insert p S) < phaseIntegral (insert m S) := by
  unfold phaseIntegral
  refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
    (continuous_phaseProduct _).continuousOn (continuous_phaseProduct _).continuousOn ?_ ?_
  · intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self hu
    rw [phaseProduct_insert hp, phaseProduct_insert hm]
    exact mul_le_mul_of_nonneg_right
      (one_sub_pow_le_one_sub_pow_of_le hu' hpm.le)
      (phaseProduct_nonneg_on_Icc S hu')
  · refine ⟨1 / 2, ?_, ?_⟩
    · constructor <;> norm_num
    · have hu : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
      rw [phaseProduct_insert hp, phaseProduct_insert hm]
      exact mul_lt_mul_of_pos_right
        (one_sub_pow_lt_one_sub_pow_of_lt hu hpm)
        (phaseProduct_pos_of_mem_Ioo hS hu)

/--
**The strict `k = 1` prime-exchange lemma.**

With `p ≥ 1`, `t ≥ 2` (so the multiple `t·p` strictly exceeds `p`), the
exponents `p`, `t·p` absent from `S`, and every remaining exponent `≥ 1`,
swapping the multiple `t·p` out for `p` *strictly* decreases `F`:

`F(S ∪ {p}) < F(S ∪ {t·p})`.
-/
theorem phaseIntegral_exchange_multiple_lt {S : Finset ℕ} {p t : ℕ}
    (hp : p ∉ S) (hm : t * p ∉ S) (hp1 : 1 ≤ p) (ht : 2 ≤ t)
    (hS : ∀ n ∈ S, 1 ≤ n) :
    phaseIntegral (insert p S) < phaseIntegral (insert (t * p) S) := by
  have hpm : p < t * p := by
    have h2p : 2 * p ≤ t * p := Nat.mul_le_mul_right p ht
    omega
  exact phaseIntegral_replace_lt hp hm hpm hS

/--
**Inserting a fresh exponent strictly decreases `F`.**

If `n` is absent from `S` and every exponent of `S` is `≥ 1`, then
`F(S ∪ {n}) < F(S)`: the new factor `1 - u^n` is `< 1` on `(0,1)` while the
remaining product stays strictly positive there. In particular the prime
truncation values strictly decrease each time a new prime enters, which is what
makes the infimum over finite antichains unattained.
-/
theorem phaseIntegral_insert_lt {S : Finset ℕ} {n : ℕ}
    (hn : n ∉ S) (hS : ∀ m ∈ S, 1 ≤ m) :
    phaseIntegral (insert n S) < phaseIntegral S := by
  unfold phaseIntegral
  refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
    (continuous_phaseProduct _).continuousOn (continuous_phaseProduct _).continuousOn ?_ ?_
  · intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self hu
    exact phaseProduct_antitone (Finset.subset_insert n S) hu'
  · refine ⟨1 / 2, ?_, ?_⟩
    · constructor <;> norm_num
    · have hu : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
      rw [phaseProduct_insert hn]
      have hP : 0 < phaseProduct S (1 / 2) := phaseProduct_pos_of_mem_Ioo hS hu
      have hfac : 1 - (1 / 2 : ℝ) ^ n < 1 := by
        have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
        linarith
      calc (1 - (1 / 2 : ℝ) ^ n) * phaseProduct S (1 / 2)
          < 1 * phaseProduct S (1 / 2) := mul_lt_mul_of_pos_right hfac hP
        _ = phaseProduct S (1 / 2) := one_mul _

end ProductInvariants
