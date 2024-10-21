import RuleSystem.Rules.Basic
import RuleSystem.Rules.Finset
import RuleSystem.Rules.Function

namespace Rule

def IsPositive {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => True
  | .negative _ => False

theorem isPositive_of_positive {n : ℕ} (tags : Tags n) : IsPositive (positive tags) := by simp [IsPositive]
theorem isPositive_of_eq_positive {n : ℕ} {tags : Tags n} {rule : Rule n} (h : rule = positive tags)
  : IsPositive rule := h ▸ isPositive_of_positive _

-- @[reducible]
-- def Positive (n : ℕ) := Subtype (@IsPositive n)
abbrev Positive (n : ℕ) := Subtype (@IsPositive n)

namespace Positive

def fromTags {n : ℕ} (tags : Tags n) : Positive n := ⟨positive tags, by simp only [IsPositive]⟩

def fromTagsEmbedding {n : ℕ} : Tags n ↪ Positive n :=
  let fromTags_inj : fromTags.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [fromTags, positive.injEq] at this
    assumption
  ⟨fromTags, fromTags_inj⟩

def fromTag {n : ℕ} (tag : Tag n) := fromTags {tag}

def fromTagEmbedding {n : ℕ} : Tag n ↪ Positive n :=
  -- TODO: Find a nicer way to prove this
  let fromTag_inj : fromTag.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [fromTag, positive.injEq] at this
    have := fromTagsEmbedding.inj' (Subtype.eq this)
    exact Finset.singleton_inj.mp this
  ⟨fromTag, fromTag_inj⟩

-- def fromTagEmbedding {n : ℕ} : Tag n ↪ Subtype (@IsPositive n) :=
--   -- TODO: Find a nicer way to prove this
--   let fromTag_inj : fromTag.Injective := by
--     intro t t' subtype_eq
--     have := Subtype.eq_iff.mp subtype_eq
--     simp only [fromTag, positive.injEq] at this
--     have := fromTagsEmbedding.inj' (Subtype.eq this)
--     exact Finset.singleton_inj.mp this
--   ⟨fromTag, fromTag_inj⟩

theorem appliesTo_fromTagEmbedding {n : ℕ} {tag : Tag n} {inst : Instance n}
  : (fromTagEmbedding tag).val.appliesTo inst = (tag ∈ inst.tags) := by
    simp only [appliesTo, fromTagEmbedding, Function.Embedding.coeFn_mk, fromTag, fromTags, Finset.singleton_subset_iff]

theorem helperA {n : ℕ} {tag : Tag n} {inst : Instance n}
  : (fromTagEmbedding tag).val.appliesTo inst = (positive {tag}).appliesTo inst := rfl

-- theorem helperB {n : ℕ} {tag : Tag n} {inst : Instance n}
--   : (positive {tag}).appliesTo inst = (tag ∈ inst.tags) := rfl

theorem helperC {n : ℕ} {tag : Tag n} {inst : Instance n}
  : (positive {tag}).appliesTo inst = ({tag} ⊆ inst.tags) := rfl

theorem appliesTo_fromTagEmbedding' {n : ℕ} {tag : Tag n} {inst : Instance n}
  -- : ((fromTagEmbedding : Tag n ↪ Subtype (@IsPositive n)) tag).val.appliesTo inst = ({tag} ⊆ inst.tags) := rfl
  : (fromTagEmbedding tag).val.appliesTo inst = ({tag} ⊆ inst.tags) := rfl

theorem helperD {n : ℕ} : (Tag n ↪ Positive n) = (Tag n ↪ Subtype (@IsPositive n)) := rfl

-- -- Positive.fromTagEmbedding tag
-- theorem fromTagEmbedding_eq_positive {n : ℕ} {tag : Tag n} : (fromTagEmbedding tag).val = positive {tag} := by
--   sorry

-- instance instCoeOutPositiveEmbeddingRuleEmbedding {α : Type*} {n : ℕ} : CoeOut (α ↪ Positive n) (α ↪ Rule n) where
--   coe f :=
--     let f' : α → Rule n := λ a ↦ f a
--     let f'_inj : f'.Injective := by
--       intro a a' h
--       simp [f'] at h
--       have := Subtype.val_inj.mp h
--       exact f.inj' this
--     ⟨f', f'_inj⟩

-- instance instCoeOutPositiveEmbeddingRuleEmbedding {α : Type*} {n : ℕ} : CoeOut (α ↪ Positive n) (α ↪ Rule n) where
--   coe f :=
--     let f' : α → Rule n := λ a ↦ f a
--     let f'_inj : f'.Injective := by
--       intro a a' h
--       simp [f'] at h
--       have := Subtype.val_inj.mp h
--       exact f.inj' this
--     ⟨f', f'_inj⟩

-- TODO: Fix this
-- theorem val_eq_positive {n : ℕ} (rule : Positive n) : rule.val = positive rule.val.tags := by
--   cases rule with
--   | positive tags => rfl

end Positive

-- TODO: Why is this not found if we don't explicitly define it here? E.g. `captureOnTagged (toPositive rule)` does not
--       type check without this
-- instance instCoeOutPositiveRules {n : ℕ} : CoeOut (Finset (Positive n)) (Rules n) := Finset.instCoeOutSubtype

end Rule
