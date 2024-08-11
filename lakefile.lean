import Lake
open Lake DSL

package "Lean-first-steps" where
  -- add package configuration options here

lean_lib «LeanFirstSteps» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-first-steps" where
  root := `Main
