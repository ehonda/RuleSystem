import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import RuleSystem.Rules.Defs

structure Instance (n : ℕ) where
  tags : Tags n

namespace Instance

def tagsEmbedding {n : ℕ} : Tags n ↪ Instance n := ⟨Instance.mk, by simp [Function.Injective]⟩

instance fintype {n : ℕ} : Fintype (Instance n) :=
  let tagsUniv : Tags n := Finset.univ
  let tagsPowerset := tagsUniv.powerset
  let elems := tagsPowerset.map tagsEmbedding

  let complete : ∀ inst : Instance n, inst ∈ elems := by
    simp [Instance, elems, tagsEmbedding, tagsPowerset, tagsUniv]

  ⟨elems, complete⟩

theorem eq_iff_tags_eq {n : ℕ} (inst inst' : Instance n) : inst = inst' ↔ inst.tags = inst'.tags := by
  cases inst; cases inst'; simp

instance instDecidableEq {n : ℕ} : DecidableEq (Instance n)
  := λ _ _ ↦ decidable_of_iff' _ (eq_iff_tags_eq _ _)

instance instDecidableTagsNonempty {n : ℕ} (inst : Instance n) : Decidable (inst.tags.Nonempty)
  := Finset.decidableNonempty

def castSucc {n : ℕ} (inst : Instance n) : Instance (n + 1) := ⟨inst.tags.map Fin.castSuccEmb⟩

def castSuccEmbedding {n : ℕ} : Instance n ↪ Instance (n + 1) :=
  ⟨castSucc, by simp [Function.Injective, castSucc, eq_iff_tags_eq]⟩

end Instance

abbrev Instances (n : ℕ) := Finset (Instance n)

namespace Instances

def castSucc {n : ℕ} : Instances n → Instances (n + 1) := Finset.map Instance.castSuccEmbedding

end Instances
