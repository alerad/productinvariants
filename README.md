# Product-Integral Invariants

Lean 4 formalization files accompanying the preprint
*Product-Integral Invariants of Exponent Sets: Subset-Sum Algebra, Stability Bounds, and a Prime-Indexed Limit*.

The formalization covers the finite product-integral invariant

```lean
F_S = ∫ u in (0 : ℝ)..1, ∏ n ∈ S, (1 - u ^ n)
```

and related monotonicity, subset-sum, directed-limit, prime-tail, signed-cube,
and certified rational polynomial-integral results.

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
