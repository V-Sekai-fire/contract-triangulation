import Lake
open Lake DSL

package «contract-triangulation» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Pinned by toolchain tag, which is how every Mathlib in this workspace is pinned:
-- contract-protocol, contract-interest-mgmt, interactor-spatial-oracle and
-- entities-lean-rebac are all on v4.34.1 against the same Lean.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

@[default_target]
lean_lib «Triangulation» where

-- Gates the axiom set rather than trusting it. Building this target is the check.
@[default_target]
lean_lib «AxiomCheck» where
