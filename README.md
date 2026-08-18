# contract-triangulation

Why a mesher that must keep its boundary cannot also bound its triangle quality, proved in
Lean 4 against Mathlib.

`interactor-triangulation` asserts two properties of every mesh it returns: every input
boundary vertex survives, and no triangle's aspect ratio passes a bound. Those are not
independent. A boundary that comes close to itself forces two mesh vertices close together,
a triangle with a short edge is a sliver, and collapsing the short edge is exactly what
boundary preservation forbids. Google FuzzTest found the case: a hexagon whose edge 0-1
passes within 7e-6 of edge 4-5 while every pair of its vertices is at least 8.9 apart.

`Triangulation/Sliver.lean` proves the part that fixes the constant.

    lo / hi ≤ aspect          -- a triangle's aspect ratio is at least longest over shortest
    aspect < R → hi / R < lo  -- so a bound on the ratio is a lower bound on edge length

The second is what the library's input validation is built on: if the boundary forces two
vertices closer than `maxEdge / R`, no triangulation meeting the bound exists, whatever the
mesher does. The threshold is derived rather than measured, which is the point of proving it
rather than tuning it.

## Build

    lake exe cache get
    lake build

## What this does not prove

That pmp's remesher achieves the bound when the boundary is well separated. That would mean
formalising the remesher, and it is not claimed here. What is proved is the obstruction: the
inputs on which no mesher can succeed, and the number that separates them.
