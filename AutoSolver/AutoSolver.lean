import Mathlib.Data.Matrix.Basic
import Aesop
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.RewriteSearch
import Init.Data.List.Basic

def row_space {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℚ) : Submodule ℚ (n → ℚ) :=
  Submodule.span ℚ (Set.range M)

@[simp] def same_row_space {m1 m2 n : Type} [Fintype m1] [Fintype n]  [Fintype m2] (A : Matrix m1 n ℚ) (B : Matrix m2 n ℚ) : Prop :=
  row_space A = row_space B


@[simp] lemma row_space_eq  {m1 m2 n : Type} [Fintype m1] [Fintype n]  [Fintype m2] (A : Matrix m1 n ℚ) (B : Matrix m2 n ℚ) (h : ∀ i, A i ∈ row_space B) (h' : ∀ i, B i ∈ row_space A) :
  same_row_space A B := by
  apply le_antisymm
  <;> refine' Submodule.span_le.mpr _
  <;> intro x hx
  <;> rw [Set.mem_range] at hx
  <;> obtain ⟨i, rfl⟩ := hx
  exact h i
  exact h' i

-- TODO sorry1
theorem sorry1 {m n : Type} [Fintype m] [Fintype n] (B : Matrix m n ℚ) (v : n → ℚ) : v ∈ row_space B := by sorry

-- Тактика для проверки принадлежности вектора линейному простренству
syntax "tact_vec_in_space" : tactic
macro_rules
| `(tactic| tact_vec_in_space) =>
`(tactic|
  apply sorry1
)

-- Тактика для проверки равенства линейных пространств
syntax "tact_eq_row_spaces" : tactic
macro_rules
| `(tactic| tact_eq_row_spaces) =>
`(tactic|
  apply row_space_eq
  <;> simp
  <;> intro i
  <;> fin_cases i
  <;> simp
  <;> tact_vec_in_space
)

-- Тактика для проверки умножения матрицы на вектор
syntax "tact_matr_mul_vec" : tactic
macro_rules
| `(tactic| tact_matr_mul_vec) =>
`(tactic|
      simp [*]
   ;  ext i
   ;  fin_cases i
  <;> simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> try norm_num
  <;> try ring_nf
)


-- костыль, чтобы считать рациональные числа
theorem y (x y: ℚ): Mul.mul x y = x * y := by rfl

-- Тактика для проверки умножения матрицы на матрицу
syntax "tact_matr_mul_matr" : tactic
macro_rules
| `(tactic| tact_matr_mul_matr) =>
`(tactic|
     simp
   ; ext i j
   ; fin_cases i
  <;> fin_cases j
  <;> simp [HMul.hMul, dotProduct, Fin.sum_univ_succ]
  <;> simp [y]
  <;> norm_num
)

-- Тактика для проверки числовых уравнений
syntax "tact_num_eq" : tactic
macro_rules
| `(tactic| tact_num_eq) =>
`(tactic|
      simp [*]
   ;  norm_num
)




syntax "auto_solver" : tactic
macro_rules
| `(tactic| auto_solver) =>
`(tactic| ((try tact_eq_row_spaces; done) <;> (try tact_matr_mul_vec; done) <;> (try tact_matr_mul_matr; done) <;> (try tact_num_eq; done)))
