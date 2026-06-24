import ProductInvariants.Finite.BlockExchangeStep
import ProductInvariants.Prime.Convergence

/-!
# `Λ` is the minimum of `F` over the descent family

This file assembles the final characterisation

  `Λ = ⨅ A ∈ 𝓐, F[A]`

where `𝓐` is the **descent family** of antichains and `Λ = directedPhaseIntegral
Nat.Prime` is the prime product-integral constant (OEIS A395518).

## What is consumed

The whole analytic crux is already proved and lives behind the single ordering
fact

  `phaseIntegral_target_le_of_descentPath : DescentPath A A₀ → F[A₀] ≤ F[A]`

(tail-domination certificate → `blockE_partial_pos` → weighted IBP engine →
`descentDiffPow ≥ 0` → iterated descent monotonicity).  In addition `Λ` is
*definitionally* the infimum of the prime truncations:

  `Lambda = ⨅ N, F[primeSetUpTo N]`        (`directedPhaseIntegral_eq_iInf`),
  `directedPhaseIntegral_le_truncation`    : `Λ ≤ F[primeSetUpTo N]`.

## The two interface obligations

The result is stated for an abstract family `𝓐 : Set (Finset ℕ)` together with
the two clearly-isolated combinatorial/`rpow` interface hypotheses (NOT hidden
`sorry`s):

* `hmem_prime` : every prime truncation `primeSetUpTo N` lies in `𝓐`
  (the prime tower is part of the family);
* `hdescend`  : every `A ∈ 𝓐` admits a `DescentPath` to some prime truncation
  `primeSetUpTo (Ndesc A)` (the combinatorial descent reaches the prime
  antichain; its analytic steps are validated by `IsSubstStepFor.subst_id`,
  now a proved theorem via the genuine `uᵖ` product algebra
  `phaseIntegral_blockStep_diff`).

Under these, `Λ` is exactly the family-wide infimum, and is *attained in the
limit* by the prime tower.
-/

open Filter

namespace ProductInvariants

variable {𝓐 : Set (Finset ℕ)}

/-- **`Λ` lower-bounds every member of the descent family.**

For `A ∈ 𝓐`, the descent `A ⟶* primeSetUpTo (Ndesc A)` gives
`F[primeSetUpTo (Ndesc A)] ≤ F[A]`, and `Λ ≤ F[primeSetUpTo (Ndesc A)]` since `Λ`
is the infimum of the prime truncations.  Chaining yields `Λ ≤ F[A]`. -/
theorem lambda_le_of_descend
    (Ndesc : Finset ℕ → ℕ)
    (hdescend : ∀ A ∈ 𝓐, DescentPath A (primeSetUpTo (Ndesc A)))
    {A : Finset ℕ} (hA : A ∈ 𝓐) :
    Lambda ≤ phaseIntegral A := by
  have hstep : phaseIntegral (primeSetUpTo (Ndesc A)) ≤ phaseIntegral A :=
    phaseIntegral_target_le_of_descentPath (hdescend A hA)
  have hLam : Lambda ≤ phaseIntegral (primeSetUpTo (Ndesc A)) := by
    have h := directedPhaseIntegral_le_truncation Nat.Prime (Ndesc A)
    simpa [Lambda, primeSetUpTo] using h
  exact le_trans hLam hstep

/-- The family phase-integrals are bounded below (by `0`), so their `iInf` is
well behaved. -/
theorem bddBelow_phaseIntegral_image (𝓐 : Set (Finset ℕ)) :
    BddBelow (Set.range fun A : 𝓐 => phaseIntegral (A : Finset ℕ)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨A, rfl⟩
  exact phaseIntegral_nonneg _

/-- **`Λ` is the infimum of `F` over the descent family.**

Given the two interface hypotheses (prime truncations are in `𝓐`; every member
descends to a prime truncation), the prime constant equals the family-wide
infimum:

  `Λ = ⨅ A : 𝓐, F[A]`.

The proof is `le_antisymm`:

* `≤` : `Λ` lower-bounds every member (`lambda_le_of_descend`), so `Λ ≤ ⨅`;
* `≥` : the prime tower `primeSetUpTo N ∈ 𝓐` gives `⨅ ≤ F[primeSetUpTo N]` for
  every `N`, hence `⨅ ≤ ⨅_N F[primeSetUpTo N] = Λ`. -/
theorem lambda_eq_iInf_descentFamily
    [Nonempty 𝓐]
    (Ndesc : Finset ℕ → ℕ)
    (hmem_prime : ∀ N, primeSetUpTo N ∈ 𝓐)
    (hdescend : ∀ A ∈ 𝓐, DescentPath A (primeSetUpTo (Ndesc A))) :
    Lambda = ⨅ A : 𝓐, phaseIntegral (A : Finset ℕ) := by
  apply le_antisymm
  · -- `Λ ≤ ⨅`: `Λ` lower-bounds every family member.
    apply le_ciInf
    rintro ⟨A, hA⟩
    exact lambda_le_of_descend Ndesc hdescend hA
  · -- `⨅ ≤ Λ`: the prime tower sits in the family, so `⨅ ≤ F[primeSetUpTo N]`,
    -- and `Λ = ⨅_N F[primeSetUpTo N]`.
    rw [Lambda, directedPhaseIntegral_eq_iInf]
    apply le_ciInf
    intro N
    have hbdd := bddBelow_phaseIntegral_image 𝓐
    have hle : (⨅ A : 𝓐, phaseIntegral (A : Finset ℕ))
        ≤ phaseIntegral ((⟨primeSetUpTo N, hmem_prime N⟩ : 𝓐) : Finset ℕ) :=
      ciInf_le hbdd _
    simpa [primeSetUpTo] using hle

/-- **`Λ` is attained in the limit by the prime tower.**

A companion to `lambda_eq_iInf_descentFamily`: the prime truncations — all
members of the family — converge to `Λ`, so the infimum is genuinely approached
along an explicit minimising sequence inside `𝓐`. -/
theorem prime_tower_tendsto_lambda_min
    (Ndesc : Finset ℕ → ℕ)
    [Nonempty 𝓐]
    (hmem_prime : ∀ N, primeSetUpTo N ∈ 𝓐)
    (hdescend : ∀ A ∈ 𝓐, DescentPath A (primeSetUpTo (Ndesc A))) :
    Tendsto (fun N => phaseIntegral (primeSetUpTo N)) atTop
      (nhds (⨅ A : 𝓐, phaseIntegral (A : Finset ℕ))) := by
  rw [← lambda_eq_iInf_descentFamily Ndesc hmem_prime hdescend]
  exact prime_truncations_tendsto_Lambda

end ProductInvariants
