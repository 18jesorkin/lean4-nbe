import Lake
open Lake DSL

package «lean4-nbe» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require verso from git
  "https://github.com/leanprover/verso.git" @ "main"

@[default_target]
lean_lib «Lean4Nbe» where
  -- add any library configuration options here

@[default_target]
lean_exe textbook where
  srcDir := "NbETextbook"
  root := `NbETextbookMain
