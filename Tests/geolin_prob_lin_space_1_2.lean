import Mathlib.Data.Matrix.Basic
import Aesop
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.RewriteSearch
import AutoSolver


@[simp] def x: List ℚ :=  [6, 2, 9]
@[simp] def e_1: List ℚ :=  [5, 0, 4]
@[simp] def e_2: List ℚ :=  [5, -1, 0]
@[simp] def e_3: List ℚ :=  [-1, 0, 4]

@[simp] def x1: ℚ := 73/24
@[simp] def x2: ℚ := -2
@[simp] def x3: ℚ := -19/24


theorem correctness: List.foldl (List.zipWith (.+.)) (List.map (x1 * .) e_1) [(List.map (x2 * .) e_2), (List.map (x3 * .) e_3)] = x := by
    auto_solver
