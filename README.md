# Product-Integral Invariants

[![Lean](https://github.com/alerad/productinvariants/actions/workflows/lean.yml/badge.svg)](https://github.com/alerad/productinvariants/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/1249538983.svg)](https://doi.org/10.5281/zenodo.21191624)

Lean 4 formalization accompanying the paper
*An extremal product integral over finite primitive sets*.

The formalization covers the finite product-integral functional

```lean
F[S] = ∫ u in (0 : ℝ)..1, ∏ n ∈ S, (1 - u ^ n)
```

and proves that the primes are extremal for `F` over finite primitive sets
(divisibility antichains), together with the supporting monotonicity,
directed-limit, prime-tail, and certified rational polynomial-integral results.

## Main results

- `lambda_eq_iInf_finiteAntichain` (`ProductInvariants/Finite/Antichain.lean`):
  `Λ` is the infimum of `F` over all finite divisibility antichains.
- `lambda_lt_phaseIntegral_antichain` (same file): the infimum is not attained.
- `prime_phase_tail_bound` (`ProductInvariants/Prime/TailBound.lean`):
  unconditional truncation tail bound.
- `phaseMetricSpace`, `phaseEnergy_subadditive`
  (`ProductInvariants/Finite/PhaseMetric.lean`): the submodular defect metric.
- `Lambda_bounds_2003` (`ProductInvariants/Certified/LambdaHighPrecision.lean`):
  exact rational sandwich certifying the first 26 decimal digits of `Λ`
  (OEIS [A395518](https://oeis.org/A395518)).

Axiom footprints are checkable with `#print axioms`: the metric and tail-bound
results use only `propext`, `Classical.choice`, `Quot.sound`; the extremal
theorem and the digit certificates additionally use `native_decide`
(`Lean.ofReduceBool`), as detailed in the paper.

## Build

Install Lean through `elan`, then run:

```sh
lake exe cache get
lake build
```

The project is pinned by `lean-toolchain` and `lake-manifest.json`.

## Layout

- `ProductInvariants/Finite`: finite product-integral definitions and bounds.
- `ProductInvariants/Directed`: directed truncation limits.
- `ProductInvariants/Prime`: prime-indexed limit and tail estimates.
- `ProductInvariants/Cube`: signed-cube and fiber cancellation results.
- `ProductInvariants/Certified`: exact rational polynomial-integral certificates.
