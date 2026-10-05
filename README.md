# contract-triangulation

A Lean 4 proof, against Mathlib, that a mesher which must keep its boundary cannot also bound its triangle quality.

## What it is for

A mesher that promises every input boundary vertex survives, and that no triangle's aspect ratio
passes a bound, is promising two things that are not independent. A boundary that comes close to
itself forces two vertices close together, a triangle with a short edge is a sliver, and the only
fix is to collapse the edge the first promise protects. The proof turns an aspect-ratio bound into
a lower bound on edge length, which gives input validation a derived threshold rather than a
tuned one. It proves the obstruction only, not that any remesher meets the bound on
well-separated input.

## Build

```sh
lake exe cache get
lake build
```

The build fails if any declaration depends on `sorry`.

## Licence

MIT; see `LICENSE`.
