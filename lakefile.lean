import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.28.0"

package «HeavyBall» where

@[default_target]
lean_lib «HeavyBall» where
