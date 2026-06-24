import ProductInvariants.Finite.BlockExchangeStep
import ProductInvariants.Finite.LambdaMin

/-!
# `Λ` is the infimum of `F` over all finite divisibility antichains

This file proves the clean characterisation

  `Λ = ⨅ A ∈ 𝓐, F[A]`

where `𝓐` is the family of **all** finite divisibility antichains in some
interval `{2,…,N}` (not just the maximal ones, and with no descent to an initial
prime *truncation*).

## The compression step

For a prime `p` and a support `A`, the **compression at `p`** collapses every
multiple of `p` in `A` into the single prime `p`:

  `compressAt p A = insert p (A.filter (¬ p ∣ ·))`.

Writing `B = A.filter (¬ p ∣ ·)` for the non-multiples and
`T = (A.filter (p ∣ ·)).image (· / p)` for the quotients of the multiples, the
block `A.filter (p ∣ ·)` is exactly `T.image (· * p)`, so a compression is a
genuine block-exchange `DescentStep A (compressAt p A)` (`DescentStep_compressAt`),
provided every multiple of `p` in `A` is `≥ 2p` (i.e. `p ∉ A`) — which holds when
`A` is an antichain containing a multiple of `p` but not `p` itself.

## Descent to a finite prime set, and the lower bound

Iterating the compression at a prime factor of a composite element strictly
lowers the sum measure, so every finite divisibility antichain descends to *some*
all-prime antichain `Q` (`antichain_descends_to_allPrime`) — **with no maximality
hypothesis**.  A finite divisibility antichain need *not* descend to an initial
prime truncation `primeSetUpTo N` (e.g. `{15}` descends to `{3}` or `{5}`,
neither a truncation), and we do not require it to: `Q` embeds in the truncation
`primeSetUpTo N` for any `N` bounding its elements, and antitonicity of `F`
(`phaseIntegral_antitone`) plus `Λ ≤ F[primeSetUpTo N]` give `Λ ≤ F[Q] ≤ F[A]`.

Combined with the prime tower lying inside `𝓐`, this yields
`lambda_eq_iInf_finiteAntichain` with no `sorry` and no `hbig`-dependent
maximality-preservation machinery.
-/

open Finset

namespace ProductInvariants

/-! ## Divisibility antichains in an interval -/

/-- `A ⊆ {2,…,N}`. -/
def InInterval (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, 2 ≤ a ∧ a ≤ N

/-- `A` is a divisibility antichain inside `{2,…,N}`: its elements lie in the
interval and no element divides another. -/
def IsDivAntichainIn (N : ℕ) (A : Finset ℕ) : Prop :=
  InInterval N A ∧
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a ∣ b ∧ ¬ b ∣ a

/-- `A` is a *maximal* divisibility antichain in `{2,…,N}`: no further element of
the interval can be added while remaining an antichain. -/
def IsMaxDivAntichainIn (N : ℕ) (A : Finset ℕ) : Prop :=
  IsDivAntichainIn N A ∧
    ∀ x, 2 ≤ x → x ≤ N → x ∉ A → ¬ IsDivAntichainIn N (insert x A)

/-! ## The compression operation -/

/-- The non-multiples of `p` in `A`. -/
def nonMultiples (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun a => ¬ p ∣ a)

/-- The quotients `a / p` of the multiples of `p` in `A`. -/
def quotientsOfMultiples (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.filter (fun a => p ∣ a)).image (fun a => a / p)

/-- The compression of `A` at `p`: collapse all multiples of `p` to the single
prime `p`. -/
def compressAt (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  insert p (nonMultiples p A)

/-- The multiples of `p` in `A` are exactly the `p`-scalings of their quotients:
`A.filter (p ∣ ·) = (quotientsOfMultiples p A).image (· * p)`. -/
theorem multiples_eq_image_quotients (p : ℕ) (A : Finset ℕ) :
    A.filter (fun a => p ∣ a) = (quotientsOfMultiples p A).image (· * p) := by
  unfold quotientsOfMultiples
  ext a
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨haA, hpa⟩
    exact ⟨a / p, ⟨a, ⟨haA, hpa⟩, rfl⟩, Nat.div_mul_cancel hpa⟩
  · rintro ⟨q, ⟨b, ⟨hbA, hpb⟩, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rwa [Nat.div_mul_cancel hpb]
    · rw [Nat.div_mul_cancel hpb]; exact hpb

/-- `· * p` is injective (for `p > 0`). -/
theorem mul_right_injOn (p : ℕ) (hp : 0 < p) (T : Finset ℕ) :
    Set.InjOn (· * p) T := by
  intro a _ha b _hb hab
  exact Nat.eq_of_mul_eq_mul_right hp hab

/-- `A` splits as its non-multiples together with the scaled quotient block. -/
theorem antichain_block_decomp (p : ℕ) (A : Finset ℕ) :
    A = nonMultiples p A ∪ (quotientsOfMultiples p A).image (· * p) := by
  rw [← multiples_eq_image_quotients]
  unfold nonMultiples
  rw [Finset.union_comm, Finset.filter_union_filter_not_eq (fun a => p ∣ a) A]

/-- The non-multiple part is disjoint from the multiple (block) part. -/
theorem disjoint_nonMultiples_block (p : ℕ) (A : Finset ℕ) :
    Disjoint (nonMultiples p A) ((quotientsOfMultiples p A).image (· * p)) := by
  rw [← multiples_eq_image_quotients]
  unfold nonMultiples
  exact (Finset.disjoint_filter_filter_not A A (fun a => p ∣ a)).symm

/-- **A compression is a genuine block-exchange descent step.**

If `p` is prime, `p ∉ A`, and `A` contains a multiple of `p`, then collapsing the
multiples of `p` to `p` is a `DescentStep A (compressAt p A)`, provided every
quotient `t = a/p` (for `a` a multiple of `p` in `A`) is `≥ 2` — which holds
exactly because `p ∉ A` forces every such `a` to be `≥ 2p`. -/
theorem DescentStep_compressAt {A : Finset ℕ} {p : ℕ}
    (hp : Nat.Prime p)
    (hquot : ∀ t ∈ quotientsOfMultiples p A, 2 ≤ t) :
    DescentStep A (compressAt p A) := by
  refine ⟨nonMultiples p A, p, quotientsOfMultiples p A, hp.one_lt.le, hquot, ?_⟩
  refine
    { block_eq := antichain_block_decomp p A
      prime_eq := rfl
      disj := disjoint_nonMultiples_block p A
      notMem := ?_
      inj := mul_right_injOn p hp.pos _ }
  -- `p ∉ nonMultiples p A` since `p ∣ p`.
  unfold nonMultiples
  simp only [Finset.mem_filter, not_and, not_not]
  intro _; exact dvd_refl p

/-- Membership in a quotient set: `t ∈ quotientsOfMultiples p A ↔ ∃ a ∈ A, p ∣ a ∧ a/p = t`. -/
theorem mem_quotientsOfMultiples {p t : ℕ} {A : Finset ℕ} :
    t ∈ quotientsOfMultiples p A ↔ ∃ a ∈ A, p ∣ a ∧ a / p = t := by
  unfold quotientsOfMultiples
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨haA, hpa⟩, rfl⟩; exact ⟨a, haA, hpa, rfl⟩
  · rintro ⟨a, haA, hpa, rfl⟩; exact ⟨a, ⟨haA, hpa⟩, rfl⟩

/-- If every element of `A` is `≥ 2` and `p ∉ A`, then every quotient `a/p`
(`a` a multiple of `p` in `A`) is `≥ 2`: the only multiple of `p` below `2p` is
`p` itself, which is excluded. -/
theorem quotients_ge_two_of_not_mem {p : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hp_not_mem : p ∉ A) :
    ∀ t ∈ quotientsOfMultiples p A, 2 ≤ t := by
  intro t ht
  obtain ⟨a, haA, hpa, rfl⟩ := mem_quotientsOfMultiples.mp ht
  have ha2 : 2 ≤ a := hpos a haA
  -- `a = (a/p)*p`, and `a ≠ p` since `p ∉ A`.
  have hane : a ≠ p := fun h => hp_not_mem (h ▸ haA)
  have hrec : a / p * p = a := Nat.div_mul_cancel hpa
  by_contra hlt
  rw [not_le] at hlt
  -- `a/p ≤ 1`; combined with `a = (a/p)·p` and `a ≥ 2`, `a ≠ p` this is impossible.
  interval_cases h : (a / p) <;> omega

/-! ## Membership in the compression -/

/-- Membership in `nonMultiples`. -/
theorem mem_nonMultiples {p a : ℕ} {A : Finset ℕ} :
    a ∈ nonMultiples p A ↔ a ∈ A ∧ ¬ p ∣ a := by
  unfold nonMultiples; exact Finset.mem_filter

/-- Membership in `compressAt`: an element is either the prime `p` or a
non-multiple of `p` already in `A`. -/
theorem mem_compressAt {p a : ℕ} {A : Finset ℕ} :
    a ∈ compressAt p A ↔ a = p ∨ (a ∈ A ∧ ¬ p ∣ a) := by
  unfold compressAt
  rw [Finset.mem_insert, mem_nonMultiples]

/-- The non-multiple part of `A` is a subset of `A`. -/
theorem nonMultiples_subset (p : ℕ) (A : Finset ℕ) : nonMultiples p A ⊆ A := by
  intro a ha; exact (mem_nonMultiples.mp ha).1

/-! ## Compression preserves the antichain structure

A compression at a prime `p` keeps the result inside the interval `{2,…,N}` and
keeps it a divisibility antichain, provided `p ≤ N` (so the freshly-inserted
prime is in range). The non-multiples are inherited from `A`; the new element
`p` neither divides nor is divided by any surviving non-multiple `b` (it cannot
divide `b` because `b` is a non-multiple of the prime `p`, and `b` cannot divide
the prime `p` because `2 ≤ b ≠ p`). -/

/-- Compression keeps every element inside `{2,…,N}`, as long as `2 ≤ p ≤ N`. -/
theorem compressAt_inInterval {N p : ℕ} {A : Finset ℕ}
    (hA : InInterval N A) (hp2 : 2 ≤ p) (hpN : p ≤ N) :
    InInterval N (compressAt p A) := by
  intro a ha
  rcases mem_compressAt.mp ha with rfl | ⟨haA, _⟩
  · exact ⟨hp2, hpN⟩
  · exact hA a haA

/-- Compression at a prime keeps the divisibility-antichain property. -/
theorem compressAt_isDivAntichain {N p : ℕ} {A : Finset ℕ}
    (hp : Nat.Prime p) (hA : IsDivAntichainIn N A) (hp2 : 2 ≤ p) (hpN : p ≤ N) :
    IsDivAntichainIn N (compressAt p A) := by
  obtain ⟨hint, hac⟩ := hA
  refine ⟨compressAt_inInterval hint hp2 hpN, ?_⟩
  intro a ha b hb hab
  rcases mem_compressAt.mp ha with hap | ⟨haA, hpa⟩ <;>
    rcases mem_compressAt.mp hb with hbp | ⟨hbA, hpb⟩
  · exact absurd (hap.trans hbp.symm) hab
  · -- `a = p`, `b` a non-multiple of `p`: `p ∤ b` and `b ∤ p`.
    subst hap
    refine ⟨hpb, ?_⟩
    intro hbp'
    -- `b ∣ p`, `p` prime ⟹ `b = 1` or `b = p`; both impossible (`2 ≤ b`, `p ∤ b`).
    rcases (Nat.dvd_prime hp).mp hbp' with h1 | hpe
    · have : 2 ≤ b := (hint b hbA).1; omega
    · exact hpb (hpe ▸ dvd_refl a)
  · -- symmetric to the previous case.
    subst hbp
    refine ⟨?_, hpa⟩
    intro hap'
    rcases (Nat.dvd_prime hp).mp hap' with h1 | hpe
    · have : 2 ≤ a := (hint a haA).1; omega
    · exact hpa (hpe ▸ dvd_refl b)
  · -- both `a, b` are non-multiples inherited from `A`.
    exact hac a haA b hbA hab

/-! ## The compression strictly lowers the sum measure

Using `∑ a ∈ A, a` as a well-founded measure: compressing at a prime `p` that
divides some element `m ∈ A` with `m ≠ p` strictly decreases the sum, because the
whole block of multiples (each `≥ 2p`) is collapsed to the single prime `p`. -/

/-- `p ∉ nonMultiples p A` because `p ∣ p`. -/
theorem prime_not_mem_nonMultiples (p : ℕ) (A : Finset ℕ) :
    p ∉ nonMultiples p A := by
  rw [mem_nonMultiples]; rintro ⟨_, h⟩; exact h (dvd_refl p)

/-- The sum over `A` splits as the non-multiple part plus the multiple block. -/
theorem sum_split_nonMultiples (p : ℕ) (A : Finset ℕ) :
    (∑ a ∈ A, a) = (∑ a ∈ nonMultiples p A, a)
        + ∑ a ∈ A.filter (fun a => p ∣ a), a := by
  unfold nonMultiples
  rw [add_comm, Finset.sum_filter_add_sum_filter_not A (fun a => p ∣ a)]

/-- **Compression strictly lowers the sum.** If `A`'s elements are all `≥ 1`,
`p ∤`-free of `p` itself (`p ∉ A` is not required), and `A` contains a multiple
`m` of `p` with `m ≠ p` (equivalently `m ≥ 2p` for `p ≥ 1`), then the compressed
support has strictly smaller sum. -/
theorem sum_compressAt_lt {p : ℕ} {A : Finset ℕ} (hp1 : 1 ≤ p)
    (hpos : ∀ a ∈ A, 1 ≤ a)
    {m : ℕ} (hmA : m ∈ A) (hpm : p ∣ m) (hmne : m ≠ p) :
    (∑ a ∈ compressAt p A, a) < ∑ a ∈ A, a := by
  classical
  -- The multiple block contains `m ≥ 2p`, so its sum is `> p`.
  have hm1 : 1 ≤ m := hpos m hmA
  have hm2p : 2 * p ≤ m := by
    obtain ⟨t, rfl⟩ := hpm
    -- `p * t ≠ p` and `p ≥ 1`, `p * t ≥ 1` force `t ≥ 2`.
    have ht2 : 2 ≤ t := by
      by_contra h
      simp only [not_le] at h
      interval_cases t <;> omega
    calc 2 * p ≤ t * p := Nat.mul_le_mul_right p ht2
      _ = p * t := Nat.mul_comm _ _
  have hmem_block : m ∈ A.filter (fun a => p ∣ a) := Finset.mem_filter.mpr ⟨hmA, hpm⟩
  have hblock_ge : p < ∑ a ∈ A.filter (fun a => p ∣ a), a := by
    have hsingle : m ≤ ∑ a ∈ A.filter (fun a => p ∣ a), a :=
      Finset.single_le_sum (f := fun a => a)
        (fun i _ => Nat.zero_le i) hmem_block
    omega
  -- The compressed sum is `p + ∑ nonMultiples` (p is not among the nonMultiples).
  have hcompress_sum : (∑ a ∈ compressAt p A, a)
      = p + ∑ a ∈ nonMultiples p A, a := by
    unfold compressAt
    rw [Finset.sum_insert (prime_not_mem_nonMultiples p A)]
  rw [hcompress_sum, sum_split_nonMultiples p A]
  omega

/-! ## Reachability: every antichain descends to an all-prime antichain

By strong induction on the sum measure: if `A` is not already all-prime, pick a
composite `m ∈ A` and a prime factor `p ∣ m`. Since `A` is an antichain and `m`
is composite (so `p ≠ m`), the prime `p` cannot itself lie in `A` (that would put
two comparable elements `p ∣ m` in `A`). Hence the compression at `p` is a valid
descent step strictly lowering the sum, and the induction hypothesis finishes. -/

/-- `A` consists entirely of primes. -/
def AllPrime (A : Finset ℕ) : Prop := ∀ a ∈ A, Nat.Prime a

/-- A composite element `m` of an antichain has a prime factor `p` that is **not**
in the antichain. (Any prime factor `p ∣ m` with `p ≠ m` would be comparable to
`m` if both lay in `A`.) -/
theorem exists_prime_factor_not_mem {N : ℕ} {A : Finset ℕ}
    (hA : IsDivAntichainIn N A) {m : ℕ} (hmA : m ∈ A) (hm_not_prime : ¬ Nat.Prime m) :
    ∃ p, Nat.Prime p ∧ p ∣ m ∧ p ≠ m ∧ p ∉ A := by
  have hm2 : 2 ≤ m := (hA.1 m hmA).1
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hpne : p ≠ m := by rintro rfl; exact hm_not_prime hp
  refine ⟨p, hp, hpm, hpne, ?_⟩
  intro hpA
  -- `p, m ∈ A`, `p ∣ m`, `p ≠ m` contradicts the antichain property.
  exact (hA.2 p hpA m hmA hpne).1 hpm

/-- **Reachability (sum-measure form).** If the antichain `A` in `{2,…,N}` has
sum `≤ s`, then it admits a descent path to an all-prime divisibility antichain in
`{2,…,N}`. -/
theorem antichain_descends_to_allPrime_aux (N : ℕ) :
    ∀ (s : ℕ) (A : Finset ℕ), (∑ a ∈ A, a) ≤ s → IsDivAntichainIn N A →
      ∃ A', AllPrime A' ∧ IsDivAntichainIn N A' ∧ DescentPath A A' := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro A hsum hA
    by_cases hall : AllPrime A
    · exact ⟨A, hall, hA, Relation.ReflTransGen.refl⟩
    · -- find a composite element `m ∈ A` and a prime factor `p ∉ A`.
      obtain ⟨m, hmA, hm_not_prime⟩ : ∃ m ∈ A, ¬ Nat.Prime m := by
        by_contra h
        simp only [not_exists, not_and, not_not] at h
        exact hall h
      obtain ⟨p, hp, hpm, hpne, hpA⟩ :=
        exists_prime_factor_not_mem hA hmA hm_not_prime
      -- `p` is a prime in range (`p ∣ m ≤ N`) not in `A`, so compression is valid.
      have hp2 : 2 ≤ p := hp.two_le
      have hm2 : 2 ≤ m := (hA.1 m hmA).1
      have hmN : m ≤ N := (hA.1 m hmA).2
      have hpN : p ≤ N := le_trans (Nat.le_of_dvd (by omega : 0 < m) hpm) hmN
      have hpos1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hA.1 a ha).1
      have hpos2 : ∀ a ∈ A, 2 ≤ a := fun a ha => (hA.1 a ha).1
      -- the descent step.
      have hquot : ∀ t ∈ quotientsOfMultiples p A, 2 ≤ t :=
        quotients_ge_two_of_not_mem hpos2 hpA
      have hstep : DescentStep A (compressAt p A) := DescentStep_compressAt hp hquot
      -- the compressed antichain stays valid and has strictly smaller sum.
      have hA' : IsDivAntichainIn N (compressAt p A) :=
        compressAt_isDivAntichain hp hA hp2 hpN
      have hsum' : (∑ a ∈ compressAt p A, a) < ∑ a ∈ A, a :=
        sum_compressAt_lt hp.one_le hpos1 hmA hpm (fun h => hpne h.symm)
      -- apply the induction hypothesis to the smaller compressed antichain.
      have hbound : (∑ a ∈ compressAt p A, a) < s := lt_of_lt_of_le hsum' hsum
      obtain ⟨A', hAllPrime, hA'anti, hpath⟩ :=
        ih (∑ a ∈ compressAt p A, a) hbound (compressAt p A) (le_refl _) hA'
      exact ⟨A', hAllPrime, hA'anti, Relation.ReflTransGen.head hstep hpath⟩

/-- **Reachability.** Every divisibility antichain in `{2,…,N}` descends to an
all-prime divisibility antichain in `{2,…,N}`. -/
theorem antichain_descends_to_allPrime {N : ℕ} {A : Finset ℕ}
    (hA : IsDivAntichainIn N A) :
    ∃ A', AllPrime A' ∧ IsDivAntichainIn N A' ∧ DescentPath A A' :=
  antichain_descends_to_allPrime_aux N (∑ a ∈ A, a) A (le_refl _) hA

/-! ## The prime truncation is a maximal antichain

The single fact about maximal antichains still needed by the (cheap, sorry-free)
characterisation below is that each prime truncation `primeSetUpTo N` is itself a
maximal divisibility antichain — this is what places the prime tower inside the
finite-antichain family for the `≥` direction of the infimum. -/

/-- Membership in `primeSetUpTo`: `a ∈ primeSetUpTo N ↔ Nat.Prime a ∧ a ≤ N`. -/
theorem mem_primeSetUpTo {a N : ℕ} :
    a ∈ primeSetUpTo N ↔ Nat.Prime a ∧ a ≤ N := by
  rw [mem_primeSetUpTo_iff]
  constructor
  · rintro ⟨_, hp, hle⟩; exact ⟨hp, hle⟩
  · rintro ⟨hp, hle⟩; exact ⟨hp.pos, hp, hle⟩

/-- The prime truncation `primeSetUpTo N` is itself a *maximal* divisibility
antichain in `{2,…,N}`: distinct primes are incomparable, and any composite
`x ≤ N` is divisible by one of its prime factors `≤ N`, which is present. -/
theorem primeSetUpTo_isMaxDivAntichainIn (N : ℕ) :
    IsMaxDivAntichainIn N (primeSetUpTo N) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- interval membership
    intro a ha
    obtain ⟨hp, hpN⟩ := mem_primeSetUpTo.mp ha
    exact ⟨hp.two_le, hpN⟩
  · -- antichain: distinct primes are incomparable
    intro a ha b hb hab
    obtain ⟨hpa, _⟩ := mem_primeSetUpTo.mp ha
    obtain ⟨hpb, _⟩ := mem_primeSetUpTo.mp hb
    constructor
    · intro hdvd; exact hab ((Nat.prime_dvd_prime_iff_eq hpa hpb).mp hdvd)
    · intro hdvd; exact hab ((Nat.prime_dvd_prime_iff_eq hpb hpa).mp hdvd).symm
  · -- maximality: a fresh `x ∈ {2,…,N}` is composite, hence comparable to a prime
    intro x hx2 hxN hxmem hanti
    -- `x ∉ primeSetUpTo N` and `x ≤ N` ⟹ `x` is not prime.
    have hxnp : ¬ Nat.Prime x := fun hp => hxmem (mem_primeSetUpTo.mpr ⟨hp, hxN⟩)
    obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
    have hpne : p ≠ x := by rintro rfl; exact hxnp hp
    have hpN : p ≤ N := le_trans (Nat.le_of_dvd (by omega) hpx) hxN
    have hpmem : p ∈ primeSetUpTo N := mem_primeSetUpTo.mpr ⟨hp, hpN⟩
    have hpins : p ∈ insert x (primeSetUpTo N) := Finset.mem_insert_of_mem hpmem
    have hxins : x ∈ insert x (primeSetUpTo N) := Finset.mem_insert_self _ _
    exact (hanti.2 p hpins x hxins hpne).1 hpx

/-! ## `Λ` lower-bounds *every* finite divisibility antichain

A finite divisibility antichain need *not* descend to an initial prime
*truncation* `primeSetUpTo N` (e.g. `{15}` descends to `{3}` or `{5}`, neither a
truncation), so we do **not** try to.  For the **lower bound** `Λ ≤ F[A]` over
*all* finite divisibility antichains it suffices to descend to *some* finite
prime set and bound that below `Λ`, using only:

* `antichain_descends_to_allPrime` — every antichain descends to *some* all-prime
  antichain `Q` (plain block collapses, no maximality, no `hbig`);
* `phaseIntegral_antitone` — `Q ⊆ primeSetUpTo N ⟹ F[primeSetUpTo N] ≤ F[Q]`;
* `directedPhaseIntegral_le_truncation` — `Λ ≤ F[primeSetUpTo N]`;
* `phaseIntegral_target_le_of_descentPath` — `F[Q] ≤ F[A]`.

The all-prime target `Q` need *not* be an initial prime truncation (e.g. `{15}`
descends to `{3}` or `{5}`), but it embeds into the truncation
`primeSetUpTo N` for any `N` bounding its elements, and antitonicity closes the
gap. -/

/-- An all-prime divisibility antichain in `{2,…,N}` is a subset of the prime
truncation `primeSetUpTo N`. -/
theorem allPrime_subset_primeSetUpTo {N : ℕ} {Q : Finset ℕ}
    (hall : AllPrime Q) (hint : InInterval N Q) :
    Q ⊆ primeSetUpTo N := by
  intro q hq
  obtain ⟨hq2, hqN⟩ := hint q hq
  exact mem_primeSetUpTo_iff.mpr ⟨by omega, hall q hq, hqN⟩

/-- **Finite all-prime set above `Λ`.** An all-prime divisibility antichain `Q`
in `{2,…,N}` satisfies `Λ ≤ F[Q]`: it embeds in `primeSetUpTo N`, so
`Λ ≤ F[primeSetUpTo N] ≤ F[Q]` by antitonicity. -/
theorem lambda_le_phaseIntegral_allPrime {N : ℕ} {Q : Finset ℕ}
    (hall : AllPrime Q) (hint : InInterval N Q) :
    Lambda ≤ phaseIntegral Q := by
  have hsub : Q ⊆ primeSetUpTo N := allPrime_subset_primeSetUpTo hall hint
  have hanti : phaseIntegral (primeSetUpTo N) ≤ phaseIntegral Q :=
    phaseIntegral_antitone hsub
  have hLam : Lambda ≤ phaseIntegral (primeSetUpTo N) := by
    have h := directedPhaseIntegral_le_truncation Nat.Prime N
    simpa [Lambda, primeSetUpTo] using h
  exact le_trans hLam hanti

/-- **`Λ` lower-bounds every finite divisibility antichain.**

Descend `A` to an all-prime antichain `Q` (`antichain_descends_to_allPrime`);
then `Λ ≤ F[Q]` (`lambda_le_phaseIntegral_allPrime`) and `F[Q] ≤ F[A]`
(`phaseIntegral_target_le_of_descentPath`).  No maximality or `hbig` is used. -/
theorem lambda_le_phaseIntegral_antichain {N : ℕ} {A : Finset ℕ}
    (hA : IsDivAntichainIn N A) :
    Lambda ≤ phaseIntegral A := by
  obtain ⟨Q, hall, hQanti, hpath⟩ := antichain_descends_to_allPrime hA
  have hlb : Lambda ≤ phaseIntegral Q :=
    lambda_le_phaseIntegral_allPrime hall hQanti.1
  have hstep : phaseIntegral Q ≤ phaseIntegral A :=
    phaseIntegral_target_le_of_descentPath hpath
  exact le_trans hlb hstep

/-! ## `Λ` is the infimum over *all* finite divisibility antichains

The cheap lower bound discharges the `≤` direction over the full family of finite
divisibility antichains, while the prime tower (a member of that family) gives
the matching `≥` direction.  This is the clean characterisation that avoids the
prime-truncation descent interface entirely. -/

/-- The **family of finite divisibility antichains**: those `A` that are
divisibility antichains in `{2,…,N}` for *some* `N`. -/
def FiniteAntichainFamily : Set (Finset ℕ) :=
  {A | ∃ N, IsDivAntichainIn N A}

/-- Every prime truncation is a finite divisibility antichain (it is even
maximal in its own interval). -/
theorem primeSetUpTo_mem_antichainFamily (N : ℕ) :
    primeSetUpTo N ∈ FiniteAntichainFamily :=
  ⟨N, (primeSetUpTo_isMaxDivAntichainIn N).1⟩

/-- The family is nonempty (`primeSetUpTo 0 = ∅` is a member). -/
instance : Nonempty (FiniteAntichainFamily) :=
  ⟨⟨primeSetUpTo 0, primeSetUpTo_mem_antichainFamily 0⟩⟩

/-- **`Λ` is the infimum of `F` over all finite divisibility antichains.**

`le_antisymm`:

* `≤` : `Λ` lower-bounds every member (`lambda_le_phaseIntegral_antichain`);
* `≥` : the prime tower `primeSetUpTo N` lies in the family, so the infimum is
  `≤ F[primeSetUpTo N]` for every `N`, hence `≤ ⨅_N F[primeSetUpTo N] = Λ`.

This characterisation uses neither maximality nor any `hbig`-dependent descent
machinery — only the plain block-collapse descent `antichain_descends_to_allPrime`
and antitonicity of `F`. -/
theorem lambda_eq_iInf_finiteAntichain :
    Lambda =
      ⨅ A : FiniteAntichainFamily, phaseIntegral (A : Finset ℕ) := by
  apply le_antisymm
  · -- `Λ ≤ ⨅`: `Λ` lower-bounds every family member.
    apply le_ciInf
    rintro ⟨A, N, hA⟩
    exact lambda_le_phaseIntegral_antichain hA
  · -- `⨅ ≤ Λ`: the prime tower sits in the family.
    rw [Lambda, directedPhaseIntegral_eq_iInf]
    apply le_ciInf
    intro N
    have hbdd := bddBelow_phaseIntegral_image FiniteAntichainFamily
    have hle : (⨅ A : FiniteAntichainFamily, phaseIntegral (A : Finset ℕ))
        ≤ phaseIntegral
            ((⟨primeSetUpTo N, primeSetUpTo_mem_antichainFamily N⟩ :
              FiniteAntichainFamily) : Finset ℕ) :=
      ciInf_le hbdd _
    simpa [primeSetUpTo] using hle

end ProductInvariants
