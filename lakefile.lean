import Lake
open Lake DSL

package "leroy" where
  version := v!"0.1.0"

lean_lib «Leroy» where
  -- add library configuration options here

@[default_target]
lean_exe "leroy" where
  root := `Main
