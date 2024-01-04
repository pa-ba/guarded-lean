import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "main"

package «guardedlean» where
  -- add package configuration options here

lean_lib «Guardedlean» where
  -- add library configuration options here

@[default_target]
lean_exe «guardedlean» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
