import RuleSystem.Rules.BigOr
import RuleSystem.Rules.Defs
import RuleSystem.Rules.Instance
import Mathlib.Data.Fintype.Basic

inductive Rule (n : ℕ) where
  | positive (tags : Tags n)
  | negative (tags : Tags n)

namespace Rule

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

def Capture {n : ℕ} (rules : Rules n) := {inst : Instance n // applyTo rules inst}

-- TODO: Use type class inference to construct some of this, i.e. `inferInstance` and the like
instance decidableAppliesTo {n : ℕ} (rule : Rule n) (inst : Instance n) : Decidable (appliesTo rule inst)
  := match rule with
    | .positive tags => Finset.instDecidableRelSubset tags inst.tags
    | .negative tags => match @Finset.decidableNonempty _ (tags ∩ inst.tags) with
      | isTrue h => isFalse (Finset.Nonempty.ne_empty h)
      | isFalse h => isTrue (Finset.not_nonempty_iff_eq_empty.mp h)

instance decidablePredAppliesTo {n : ℕ} (rule : Rule n) : DecidablePred (appliesTo rule)
  := λ inst ↦ decidableAppliesTo rule inst

-- TODO: This looks like a prime candidate for type class inference (if used correctly?)
instance decidableApplyTo {n : ℕ} (rules : Rules n) (inst : Instance n) : Decidable (applyTo rules inst) :=
  match @Finset.decidableExistsAndFinset _ rules (appliesTo · inst) _ with
    | isTrue h => isTrue h
    | isFalse h => isFalse h

instance decidablePredApplyTo {n : ℕ} (rules : Rules n) : DecidablePred (applyTo rules)
  := λ inst ↦ decidableApplyTo rules inst

-- failed to synthesize
--   DecidablePred fun inst ↦ applyTo rules inst
def capture {n : ℕ} (rules : Rules n) : Finset (Instance n) := {inst | applyTo rules inst}

-- n : ℕ
-- rule : Negative n
-- inst : Instance n
-- h_inst : Finset.Nonempty inst.tags
-- h : ∃ a ∉ Rule.tags ↑rule, a ∈ inst.tags
-- rule✝ : Rule n
-- tags : Tags n
-- h_neg : ↑rule = Rule.negative tags
-- ⊢ tags ∩ inst.tags = ∅
--
-- ❌ THIS IS WRONG! Therefore we can't prove it.
-- 📜 NOTE: We can prove the weaker `mpr`
theorem helper_iff
    {n : ℕ}
    (rule : Negative n)
    (inst : Instance n)
    (inst_tags_nonempty : inst.tags.Nonempty)
  : (∃ tag ∉ Rule.tags rule.val, tag ∈ inst.tags) ↔ (Rule.tags rule.val) ∩ inst.tags = ∅ := by
    constructor
    · intro exists_not_mem_rule_val_tags_mem_inst_tags
      obtain ⟨tag, tag_not_mem_rule_val_tags, tag_mem_inst_tags⟩ := exists_not_mem_rule_val_tags_mem_inst_tags
      sorry
    · sorry

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
-- This theorem is about how `appliesTo` and `applyTo` are related for a negative rule and its positive counterpart(s).
-- It essentially means we can turn a negative rule into n positive rules, but not the other way around. To illustrate,
-- here are two examples:
--
-- (I) Negative rule to positive rules:
--
-- Tag Universe: {A, B, C, D, E}
-- Negative Rule: N {B, C}
-- Positive Rules: [P0 {A}, P1 {D}, P2 {E}]
-- Instances: I0 {A}, I1 {C, D}, I2 {B}
--
-- We then have:
--    appliesTo (N {B, C}) (I0 {A}) = True (Since {B, C} ∩ {A} = ∅)
--    appliesTo (N {B, C}) (I1 {C, D}) = False (Since {B, C} ∩ {C, D} = {C} ≠ ∅)
--    appliesTo (N {B, C}) (I2 {B}) = False (Since {B, C} ∩ {B} = {B} ≠ ∅)
--
-- While for the positive rules:
--    applyTo [P0 {A}, P1 {D}, P2 {E}] (I0 {A}) = appliesTo (P0 {A}) (I0 {A}) = True (Since {A} ⊆ {A})
--
--    🆘 THIS IS A PROBLEM! The implication still holds since `False → True`, but it's not what we actually want! We
--    want truth values to be the same.
--    applyTo [P0 {A}, P1 {D}, P2 {E}] (I1 {C, D}) = appliesTo (P0 {A}) (I1 {C, D}) = True (Since {A} ⊆ {C, D})
--
-- ❌ THIS IS WRONG! Therefore we can't prove it.
-- 📜 NOTE: We can only prove the weaker
--      `appliesTo rule.val inst → applyTo ((toPositive rule).map (Function.Embedding.subtype _)) inst`
--     but it is also not exactly what we want in the end.
theorem appliesTo_iff_toPositive_applyTo {n : ℕ} (rule : Negative n) (inst : Instance n) (h_inst : inst.tags.Nonempty) :
  appliesTo rule.val inst ↔ applyTo ((toPositive rule).map (Function.Embedding.subtype _)) inst := by
    simp [appliesTo, applyTo, toPositive]
    constructor
    -- TODO: Unify these two identical branches
    · intro h
      split at h
      case _ _ tags h_eq =>
        have isPositive : Rule.IsPositive rule.val := by simp only [h_eq, IsPositive]
        have isNegative : Rule.IsNegative rule.val := rule.property
        exact False.elim (false_of_isPositive_of_isNegative isPositive isNegative)
      case _ _ tags h_eq =>
        have : Rule.tags rule.val = tags := by sorry
        rw [← this] at h
        exact (helper_iff rule inst h_inst).mpr h
        -- obtain ⟨tag, tag_mem_inst_tags⟩ := h_inst
        -- exists tag
        -- constructor
        -- -- TODO: There's got to be an easier way to get here
        -- · have : tag ∉ tags := by
        --     by_contra tag_mem_tags
        --     have tag_mem_inter : tag ∈ tags ∩ inst.tags := Finset.mem_inter_of_mem tag_mem_tags tag_mem_inst_tags
        --     simp [h] at tag_mem_inter
        --   simp [h_eq, Rule.negative, Rule.tags]
        --   assumption
        -- · assumption
    · intro h
      split
      case _ _ tags h_pos =>
        have isPositive : Rule.IsPositive rule.val := by simp only [h_pos, IsPositive]
        have isNegative : Rule.IsNegative rule.val := rule.property
        exact False.elim (false_of_isPositive_of_isNegative isPositive isNegative)
      case _ _ tags h_neg =>
        have : Rule.tags rule.val = tags := by sorry
        rw [← this]
        exact (helper_iff rule inst h_inst).mp h

-- This is the weaker variant of the (incorrect) theorem above. What we can show is that for negative rules with exactly
-- one tag, we have a correspondence on the capture between the rule and its positive counterparts. Example:
--
-- Tag Universe: {A, B, C, D, E}
-- Negative Rule: N {C}
-- Positive Rules: [P0 {A}, P1 {B}, P2 {D}, P3 {E}]
-- Instances: I0 {A}, I1 {C, D}, I2 {B}
--
-- We then have:
--    appliesTo (N {C}) (I0 {A}) = True (Since {C} ∩ {A} = ∅)
--    appliesTo (N {C}) (I1 {C, D}) = False (Since {C} ∩ {C, D} = {C} ≠ ∅)
--    appliesTo (N {C}) (I2 {B}) = True (Since {C} ∩ {B} = ∅)
--
-- While for the positive rules:
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I0 {A}) = appliesTo (P0 {A}) (I0 {A}) = True (Since {A} ⊆ {A})
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I1 {C, D}) = appliesTo (P2 {D}) (I1 {C, D}) = True (Since {D} ⊆ {C, D})
--
--    🆘 THIS IS AGAIN A PROBLEM! We end up with different caputes. The problem really seem to be instances with more
--    than one tag. When constructing positive rules, these pose a problem where they intersect with the tags protected
--    by the negative rule. We also can't exclude the positive rules for the extra tags, e.g `P2 {D}` either because
--    then we fail the instance `I3 {D}`, which is captured by `N {C}` (but not by the positive rules if we exclude
--    `P2`).
--
-- ❌ THIS IS WRONG! Therefore we can't prove it.
-- 📜 NOTE: We can only prove the weaker
--      `Capture {rule.val} ⊆ Capture ((toPositive rule).map (Function.Embedding.subtype _))`
--     but it is also not exactly what we want in the end.
theorem singleton_toPositive_capture_eq
    {n : ℕ}
    (rule : Negative n)
    (inst : Instance n)
    (h_rule : ∃ tag, rule.val = Rule.negative {tag})
    -- TODO: Required?
    (h_inst : inst.tags.Nonempty)
    -- TODO: There's got to be a better way to go from `Finset (Positive n)` (`toPositive rule`) to
    --       `Finset (Rule n) = Rules n` (which is what `Capture` expects)
  : Capture {rule.val} = Capture ((toPositive rule).map (Function.Embedding.subtype _)) := by
    sorry

-- This is again the weaker variant of the (incorrect and weaker) theorem above. What we can show is that for negative
-- rules with exactly one tag, we have a correspondence on the capture between the rule and its positive counterparts,
-- by virtue of the positive rules capturing at least the same instances as the negative rule. Example:
--
-- Tag Universe: {A, B, C, D, E}
-- Negative Rule: N {C}
-- Positive Rules: [P0 {A}, P1 {B}, P2 {D}, P3 {E}]
-- Instances: I0 {A}, I1 {C, D}, I2 {B}
--
-- We then have:
--    appliesTo (N {C}) (I0 {A}) = True (Since {C} ∩ {A} = ∅)
--    appliesTo (N {C}) (I1 {C, D}) = False (Since {C} ∩ {C, D} = {C} ≠ ∅)
--    appliesTo (N {C}) (I2 {B}) = True (Since {C} ∩ {B} = ∅)
--    -> Capture {N {C}} = [I0 {A}, I2 {B}]
--
-- While for the positive rules:
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I0 {A}) = appliesTo (P0 {A}) (I0 {A}) = True (Since {A} ⊆ {A})
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I1 {C, D}) = appliesTo (P2 {D}) (I1 {C, D}) = True (Since {D} ⊆ {C, D})
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I2 {B}) = appliesTo (P1 {B}) (I2 {B}) = True (Since {B} ⊆ {B})
--    -> Capture [P0 {A}, P1 {B}, P2 {D}, P3 {E}] = [I0 {A}, I1 {C, D}, I2 {B}] ⊇ [I0 {A}, I2 {B}] = Capture {N {C}}
--
-- TODO: ⏺ Proof this
theorem singleton_toPositive_capture_sub
    {n : ℕ}
    (rule : Negative n)
    (inst : Instance n)
    (h_rule : ∃ tag, rule.val = Rule.negative {tag})
    -- TODO: Required?
    (h_inst : inst.tags.Nonempty)
    -- TODO: There's got to be a better way to go from `Finset (Positive n)` (`toPositive rule`) to
    --       `Finset (Rule n) = Rules n` (which is what `capture` expects)
  -- TODO: We can't use ⊆ here, what do we use instead?
  : capture {rule.val} ⊆ capture ((toPositive rule).map (Function.Embedding.subtype _)) := by
    sorry

end Rule
