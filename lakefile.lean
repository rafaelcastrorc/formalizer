import Lake
open Lake DSL

package «auto-blueprint-formalization» where
  -- This Lake project exists so Auto-Blueprint can run Lean as a real critic.
  -- Generated proof attempts are disposable files checked with `lake env lean`.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib AutoBlueprint where
