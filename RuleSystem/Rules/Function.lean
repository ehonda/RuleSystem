import Mathlib.Logic.Embedding.Basic

namespace Function

universe u v

-- TODO: Does this exist in mathlib? Should we contribute it?
instance instCoeOutSubtypeEmbeddingEmbedding {α : Sort u} {β : Sort v} {p : β → Prop} : CoeOut (α ↪ Subtype p) (α ↪ β) where
  coe f :=
    let f' : α → β := λ a ↦ f a
    let f'_inj : f'.Injective := by
      intro a a' h
      simp [f'] at h
      have := Subtype.val_inj.mp h
      exact f.inj' this
    ⟨f', f'_inj⟩

end Function
