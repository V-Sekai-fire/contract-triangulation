import Lake
open Lake DSL

package «contract-triangulation» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Pinned by toolchain tag, which is how every Mathlib in this workspace is pinned:
-- contract-protocol, contract-interest-mgmt, interactor-spatial-oracle and
-- entities-lean-rebac are all on v4.30.0 against the same Lean.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

@[default_target]
lean_lib «Triangulation» where
