import ProductInvariants.Finite.TailDomination16
import ProductInvariants.Finite.BlockExchangeK2

/-!
# The universal block integrand `E_S` and its partial positivity

This file packages the just-proven universal partial positivity
(`block_partial_pos_of_two_le`) in the *block-integrand* form used by the
abstract block-exchange architecture (`BlockExchange.lean`,
`BlockExchangeK2.lean`).

For a finite antichain support `S ⊆ {2,3,…}` the **block integrand** is

  `blockE S v = ∏_{t∈S}(1 - vᵗ) - (1 - v) = phaseProduct S v - (1 - v)`,

and the load-bearing statement is the *partial* (variable upper limit)
positivity

  `0 < ∫₀ᶜ blockE S v dv`   for all `c ∈ (0,1]`.

The shape-`(2,3)` prototype `BlockExchangeK2.lean` proved this via the abstract
single-crossing lemma (`Phi23_pos_via_layer1`).  Here we obtain the **same
conclusion for every `S`** directly from the tail-domination certificate, with
no per-shape root-uniqueness input.  The `(2,3)` case is recovered as a sanity
check (`blockE_two_three_eq_E23`, `blockE_partial_pos_two_three`).
-/

open MeasureTheory intervalIntegral

namespace ProductInvariants

/-- The block-exchange integrand attached to a finite support `S`:
`blockE S v = phaseProduct S v - (1 - v)`. -/
def blockE (S : Finset ℕ) (v : ℝ) : ℝ := phaseProduct S v - (1 - v)

/-- **Universal partial positivity of the block integrand.**

For every finite support `S` of integers `≥ 2` and every `c ∈ (0,1]`,

  `0 < ∫₀ᶜ blockE S v dv`.

This is the universal form of the deep block-exchange positivity crux, obtained
from the tail-domination certificate `block_partial_pos_of_two_le` with **no**
per-shape single-crossing / root-uniqueness hypothesis. -/
theorem blockE_partial_pos {S : Finset ℕ} (hS : ∀ n ∈ S, 2 ≤ n)
    {c : ℝ} (hc : c ∈ Set.Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0 : ℝ)..c, blockE S v := by
  unfold blockE
  exact block_partial_pos_of_two_le hS hc

/-! ## Sanity check: recovering the `(2,3)` prototype -/

/-- The general integrand `blockE {2,3}` agrees with the prototype `E23`. -/
theorem blockE_two_three_eq_E23 (v : ℝ) : blockE {2, 3} v = E23 v := by
  unfold blockE E23
  rw [phaseProduct_two_three]

/-- The `(2,3)` instance of the universal partial positivity, stated for the
prototype integrand `E23`.  This now follows from the universal route, matching
`Phi23_pos_via_layer1` (which used the single-crossing route). -/
theorem blockE_partial_pos_two_three {c : ℝ} (hc : c ∈ Set.Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0 : ℝ)..c, E23 v := by
  have h := blockE_partial_pos
    (S := ({2, 3} : Finset ℕ))
    (fun n hn => by fin_cases hn <;> norm_num) hc
  have hcongr :
      (∫ v in (0 : ℝ)..c, blockE {2, 3} v) = ∫ v in (0 : ℝ)..c, E23 v := by
    apply intervalIntegral.integral_congr
    intro v _hv
    exact blockE_two_three_eq_E23 v
  rwa [hcongr] at h

end ProductInvariants
