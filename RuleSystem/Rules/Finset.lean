import Mathlib.Data.Finset.Image

namespace Finset

-- TODO: Why does this not exist in mathlib?
-- TODO: Is `α : Type*` correct or can we make it `α : Sort u`?
instance instCoeOutSubtype {α : Type*} {p : α → Prop} : CoeOut (Finset (Subtype p)) (Finset α) where
  coe := map (Function.Embedding.subtype _)

end Finset
