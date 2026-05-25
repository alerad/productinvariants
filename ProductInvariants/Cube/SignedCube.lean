import ProductInvariants.Finite.PowersetExpansion

namespace ProductInvariants

abbrev cubeVertices (S : Finset ℕ) : Finset (Finset ℕ) :=
  S.powerset

theorem cube_phaseProduct_shadow (S : Finset ℕ) (u : ℝ) :
    phaseProduct S u =
      ∑ A ∈ cubeVertices S, subsetSign A * u ^ subsetSum A :=
  phaseProduct_powersetExpansion S u

theorem cube_phaseIntegral_shadow (S : Finset ℕ) :
    phaseIntegral S =
      ∑ A ∈ cubeVertices S, subsetSign A / (1 + (subsetSum A : ℝ)) :=
  phaseIntegral_eq_sum_powerset S

end ProductInvariants
