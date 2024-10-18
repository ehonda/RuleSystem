import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import RuleSystem.Rules.Defs

structure Instance (n : ℕ) where
  tags : Tags n

namespace Instance

def mkEmbedding {n : ℕ} : Tags n ↪ Instance n := ⟨Instance.mk, by simp [Function.Injective]⟩

instance fintype {n : ℕ} : Fintype (Instance n) :=
  let tagsUniv : Tags n := Finset.univ
  let tagsPowerset := tagsUniv.powerset
  let elems := tagsPowerset.map mkEmbedding

  let complete : ∀ inst : Instance n, inst ∈ elems := by
    simp [Instance, elems, mkEmbedding, tagsPowerset, tagsUniv]

  ⟨elems, complete⟩

theorem eq_iff_tags_eq {n : ℕ} (inst inst' : Instance n) : inst = inst' ↔ inst.tags = inst'.tags := by
  cases inst; cases inst'; simp

instance instDecidableEq {n : ℕ} : DecidableEq (Instance n)
  := λ _ _ ↦ decidable_of_iff' _ (eq_iff_tags_eq _ _)

instance instDecidableTagsNonempty {n : ℕ} (inst : Instance n) : Decidable (inst.tags.Nonempty)
  := Finset.decidableNonempty

end Instance
