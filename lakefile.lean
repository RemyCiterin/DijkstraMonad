import Lake
open Lake DSL

package «dijkstraMonad» {
  -- add package configuration options here
}

lean_lib «DijkstraMonad» {
  -- add library configuration options here
}

@[default_target]
lean_exe «dijkstraMonad» {
  root := `Main
}
