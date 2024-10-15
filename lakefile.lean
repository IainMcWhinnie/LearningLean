import Lake
open Lake DSL

package "LearningLean" where
  version := v!"0.1.0"

lean_lib «LearningLean» where
  -- add library configuration options here

@[default_target]
lean_exe "learninglean" where
  root := `Main
