import ProductInvariants.Eta.FiniteMoments

namespace ProductInvariants

open scoped Topology

/-!
# Closed-form eta-product benchmark targets

This file records two classical closed-form targets suggested by Euler's
pentagonal number theorem and the Mittag-Leffler expansion of the cosecant.
The identities themselves require classical infinite-series machinery not yet
formalized here; the definitions below provide stable targets for the finite
product-integral formalization and for LeanCert numerical certificates.
-/

/-- The closed form expected for the full positive-integer exponent limit. -/
noncomputable def allExponentClosedForm : ℝ :=
  Real.pi * Real.sqrt ((48 : ℝ) / 23) *
    Real.sinh (Real.pi * Real.sqrt 23 / 3) /
      Real.cosh (Real.pi * Real.sqrt 23 / 2)

/-- The closed form expected for the even positive-integer exponent limit. -/
noncomputable def evenExponentClosedForm : ℝ :=
  Real.pi * Real.sqrt ((12 : ℝ) / 11) *
    Real.sinh (Real.pi * Real.sqrt 11 / 3) /
      Real.cosh (Real.pi * Real.sqrt 11 / 2)

/-- The finite prefix `{2, 4, ..., 2N}` of the even exponent system. -/
def evenExponentPrefix (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).image fun n => 2 * n

@[simp]
theorem mem_evenExponentPrefix {n N : ℕ} :
    n ∈ evenExponentPrefix N ↔ ∃ k, k ≤ N ∧ n = 2 * k := by
  unfold evenExponentPrefix
  simp only [Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · intro h
    rcases h with ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · intro h
    rcases h with ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

/--
Future theorem target: Euler pentagonal theorem plus the cosecant
Mittag-Leffler expansion should identify the all-exponent product-integral
limit with `allExponentClosedForm`.
-/
def allExponentLimit_eq_closedForm_target : Prop :=
  Filter.Tendsto (fun N : ℕ => phaseIntegral (etaPrefix N))
    Filter.atTop (𝓝 allExponentClosedForm)

/--
Future theorem target: the same pentagonal/cosecant method applied after the
substitution `v = u^2` should identify the even-exponent product-integral limit
with `evenExponentClosedForm`.
-/
def evenExponentLimit_eq_closedForm_target : Prop :=
  Filter.Tendsto (fun N : ℕ => phaseIntegral (evenExponentPrefix N))
    Filter.atTop (𝓝 evenExponentClosedForm)

end ProductInvariants
