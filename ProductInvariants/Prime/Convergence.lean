import ProductInvariants.Directed.Limit
import ProductInvariants.Prime.Basic

namespace ProductInvariants

theorem prime_truncations_tendsto_Lambda :
    Filter.Tendsto
      (fun N => phaseIntegral (primeSetUpTo N))
      Filter.atTop
      (nhds Lambda) := by
  simpa [primeSetUpTo, Lambda] using
    truncation_tendsto_directedPhaseIntegral Nat.Prime

end ProductInvariants
