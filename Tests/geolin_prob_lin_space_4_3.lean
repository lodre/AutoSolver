import AutoSolver

@[simp]
def f: ℚ → ℚ → ℚ → ℚ := (4 * . + 2 * . + .)

@[simp]
def e1: Fin 3 -> ℚ := ![5, 0, 4]
@[simp]
def e2: Fin 3 -> ℚ := ![5, -1, 0]
@[simp]
def e3: Fin 3 -> ℚ := ![-1, 0, 4]

@[simp]
def apply_f (e: Fin 3 → ℚ) := f (e 0) (e 1) (e 2)

theorem new_basis: List.map apply_f [e1, e2, e3] = [24, 18, 0] := by
  auto_solver
