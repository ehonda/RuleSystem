import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Embedding.Basic

namespace Fin

theorem false_of_castLE_eq_last {n : ℕ} {x : Fin n} (h : Fin.castLE (by simp) x = Fin.last n) : False := by
  simp [castLE, last] at h
  exact Nat.ne_of_lt x.isLt h

end Fin
