import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.RewriteSearch
import AutoSolver



@[simp] def x_1: Fin 4 → ℚ := ![-1, 4, -3, -2]
@[simp] def x_2: Fin 4 → ℚ := ![3, -7, 5, 3]
@[simp] def x_3: Fin 4 → ℚ := ![3, -2, 1, 0]
@[simp] def x_4: Fin 4 → ℚ := ![-4, 1, 0, 1]

@[simp] def matrix_1: Matrix (Fin 4) (Fin 4) ℚ := Matrix.of ![x_1, x_2, x_3, x_4]

@[simp] def matrix_2: Matrix (Fin 4) (Fin 4) ℚ := Matrix.of ![
  ![-1, 4, -3, -2],
  ![0, 5, -4, -3],
  ![0, 10, -8, -6],
  ![0, -15, 12, 9]
]
theorem matrix_1_row_eq_matrix_2_row : same_row_space matrix_1 matrix_2 := by
  auto_solver

@[simp] def matrix_3: Matrix (Fin 3) (Fin 4) ℚ := Matrix.of ![
  ![-1, 4, -3, -2],
  ![0, 5, -4, -3],
  ![0, 0, -4/5, 9/5]
]

theorem matrix_2_row_eq_matrix_3_row : same_row_space matrix_2 matrix_3 := by
  auto_solver



-- theorem matrix_1_row_eq_matrix_2_row : row_space matrix_1 = row_space matrix_2 := by
--   simp
--   apply le_antisymm
--   <;> intro v h
--   <;> simp_all [Submodule.span]
--   <;> intro p
--   <;> have hp := h p
--   <;> intro hr
--   <;> apply hp
--   <;> simp_all [Set.range]
--   <;> intro x hx
--   <;> apply hr
--   <;> simp_all
--   <;> obtain ⟨y1, hx⟩ := hx
--   <;> rw [← hx]
--   <;> constructor
--   <;> subst hx
--   <;>
