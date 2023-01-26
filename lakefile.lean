import Lake
open Lake DSL

package «dijkstraMonad» {
  -- add package configuration options here
}

lean_lib «DijkstraMonad» {
  -- add library configuration options here
}

--@[default_target]
--lean_exe «dijkstraMonad» {
--  root := `Main
--}
-- f759a3662ca93422c3c8281852dc352f9a7b5399
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"f759a3662ca93422c3c8281852dc352f9a7b5399"
