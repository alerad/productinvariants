import ProductInvariants.Directed.Predicate

namespace ProductInvariants

def primeSetUpTo (N : ℕ) : Finset ℕ :=
  truncationSet Nat.Prime N

noncomputable def Lambda : ℝ :=
  directedPhaseIntegral Nat.Prime

@[simp]
theorem primeSetUpTo_eq_truncationSet (N : ℕ) :
    primeSetUpTo N = truncationSet Nat.Prime N := rfl

end ProductInvariants
