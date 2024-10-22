import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Embedding.Basic

namespace Fin

-- We don't need this as there is `Fin.castSuccEmb` in mathlib. We keep the file around for now in case we need other
-- auxiliary definitions.

-- def castSuccEmbedding {n : ℕ} : Fin n ↪ Fin (n + 1) :=
--   ⟨castSucc, @castSucc_injective _⟩

end Fin
