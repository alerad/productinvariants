import ProductInvariants.Directed.Predicate

namespace ProductInvariants

theorem truncation_tendsto_directedPhaseIntegral
    (A : ℕ → Prop) [DecidablePred A] :
    Filter.Tendsto
      (fun N => phaseIntegral (truncationSet A N))
      Filter.atTop
      (nhds (directedPhaseIntegral A)) := by
  rw [directedPhaseIntegral_eq_iInf]
  exact tendsto_atTop_ciInf (truncation_phaseIntegral_antitone A)
    ⟨0, by
      rintro x ⟨N, rfl⟩
      exact phaseIntegral_nonneg (truncationSet A N)⟩

end ProductInvariants
