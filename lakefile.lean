import Lake
open Lake DSL

package «group_ac» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require «doc-gen4» from "../doc-gen4"

-- require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

@[default_target]
lean_lib «GroupAc» where
  -- add any library configuration options here
