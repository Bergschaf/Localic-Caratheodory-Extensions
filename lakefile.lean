import Lake
open Lake DSL

package "leroy" where
  version := v!"0.1.0"

lean_lib «Leroy» where
  -- add library configuration options here

@[default_target]
lean_exe "leroy" where
  root := `Main

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"