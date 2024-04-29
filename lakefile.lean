import Lake
open Lake DSL

package «Arrow» where
  -- add package configuration options here

lean_lib «Arrow» where
  -- add library configuration options here

require mathlib from
  git "https://github.com/leanprover-community/mathlib4" @ "stable"

@[default_target]
lean_lib «arrow» where
  roots := #[`Arrow]
