import RuleSystem.Rules.BigOr
import RuleSystem.Rules.Defs
import RuleSystem.Rules.Instance
import Mathlib.Data.Fintype.Basic

namespace Rule

inductive Rule (n : ℕ) where
  | positive (tags : Tags n)
  | negative (tags : Tags n)

abbrev Rules (n : ℕ) := Finset (Rule n)

-- TODO: Is there a better way to extract the tags?
def tags {n : ℕ} (rule : Rule n) : Tags n :=
  match rule with
  | .positive tags => tags
  | .negative tags => tags

def appliesTo {n : ℕ} (rule : Rule n) (inst : Instance n) : Prop :=
  match rule with
  | .positive tags => tags ⊆ inst.tags
  | .negative tags => tags ∩ inst.tags = ∅

-- TODO: Better name
def applyTo {n : ℕ} (rules : Rules n) (inst : Instance n) : Prop :=
  ∃ rule ∈ rules, (appliesTo · inst) rule

-- TODO: Helpers like `Positive.fromTags` and `Negative.fromTags`, so we can just write `Positive.fromTags tags` etc.

def IsPositive {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => True
  | .negative _ => False

def Positive (n : ℕ) := {rule : Rule n // IsPositive rule}

def IsNegative {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => False
  | .negative _ => True

def Negative (n : ℕ) := {rule : Rule n // IsNegative rule}

theorem false_of_isPositive_of_isNegative
    {n : ℕ}
    {rule : Rule n}
    (h_pos : IsPositive rule)
    (h_neg : IsNegative rule)
  : False := by cases rule with
    | positive => exact h_neg
    | negative => exact h_pos

def toPositive {n : ℕ} (rule : Negative n) : Finset (Positive n) :=
  let tags' := Finset.univ \ Rule.tags rule.val
  let ctor : Tag n → Positive n := λ (tag : Tag n) ↦ let rule := Rule.positive {tag}
    ⟨rule, by simp only [Rule.IsPositive]⟩
  let ctor_inj : ctor.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [Rule.positive.injEq, Finset.singleton_inj] at this
    assumption
  Finset.map ⟨ctor, ctor_inj⟩ tags'

-- TODO: Do we need `h_inst`?
theorem appliesTo_iff_toPositive_applyTo {n : ℕ} (rule : Negative n) (inst : Instance n) (h_inst : inst.tags.Nonempty) :
  appliesTo rule.val inst ↔ applyTo ((toPositive rule).map (Function.Embedding.subtype _)) inst := by
    simp [appliesTo, applyTo, toPositive]
    constructor
    · intro h
      split at h
      case _ _ tags h_eq =>
        have isPositive : Rule.IsPositive rule.val := by simp only [h_eq, IsPositive]
        have isNegative : Rule.IsNegative rule.val := rule.property
        exact False.elim (false_of_isPositive_of_isNegative isPositive isNegative)
      case _ _ tags h_eq =>
        obtain ⟨tag, tag_mem_inst_tags⟩ := h_inst
        exists tag
        constructor
        -- TODO: There's got to be an easier way to get here
        · have : tag ∉ tags := by
            by_contra tag_mem_tags
            have tag_mem_inter : tag ∈ tags ∩ inst.tags := Finset.mem_inter_of_mem tag_mem_tags tag_mem_inst_tags
            simp [h] at tag_mem_inter
          simp [h_eq, Rule.negative, Rule.tags]
          assumption
        · assumption
    · sorry

end Rule
