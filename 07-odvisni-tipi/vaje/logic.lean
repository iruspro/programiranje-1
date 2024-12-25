-- Izomorfizmi
open Classical

theorem eq1 {A B : Prop} : (A ∧ B) ↔ (B ∧ A) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact h.right
    . exact h.left
  . intro h
    apply And.intro
    . exact h.right
    . exact h.left

theorem eq2 {A B : Prop} : (A ∨ B) ↔ (B ∨ A) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl ha =>
      apply Or.inr
      exact ha
    | inr hb =>
      apply Or.inl
      exact hb
  . intro h
    cases h with
    | inl ha =>
      apply Or.inr
      exact ha
    | inr hb =>
      apply Or.inl
      exact hb

theorem eq3 {A B C : Prop} : (A ∧ (B ∧ C)) ↔ (B ∧ (A ∧ C)) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact h.right.left
    . apply And.intro
      . exact h.left
      . exact h.right.right
  . intro h
    apply And.intro
    . exact h.right.left
    . apply And.intro
      . exact h.left
      . exact h.right.right

theorem eq4 {A B C : Prop} : (A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C)) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl ha =>
      apply Or.inr
      apply Or.inl
      exact ha
    | inr hb =>
      cases hb with
      | inr haa =>
        apply Or.inr
        apply Or.inr
        exact haa
      | inl hbb =>
        apply Or.inl
        exact hbb
  . intro h
    cases h with
    | inl ha =>
    apply Or.inr
    apply Or.inl
    exact ha
    | inr hb =>
      cases hb with
      | inl haa =>
        apply Or.inl
        exact haa
      | inr hbb =>
        apply Or.inr
        apply Or.inr
        exact hbb

theorem eq5 {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hA hBC =>
      cases hBC with
      | inl hB =>
        apply Or.inl
        apply And.intro
        . exact hA
        . exact hB
      | inr hC =>
        apply Or.inr
        apply And.intro
        . exact hA
        . exact hC
  . intro h
    cases h with
    | inl hAB =>
      cases hAB with
      | intro hA hB =>
        apply And.intro
        . exact hA
        . apply Or.inl
          exact hB
    | inr hAC =>
      cases hAC with
      | intro hA hC =>
        apply And.intro
        . exact hA
        . apply Or.inr
          exact hC

theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro hb
      apply h
      apply Or.inl
      exact hb
    . intro hc
      apply h
      apply Or.inr
      exact hc
  . intro h
    cases h with
    | intro hBA hCA =>
      intro hBC
      cases hBC with
      | inl hB =>
        apply hBA
        exact hB
      | inr hC =>
        apply hCA
        exact hC

theorem eq7 {A B C : Prop} : C → (A ∧ B) ↔ (C → A) ∧ (C → B) := by
  apply Iff.intro
  . intro h
    constructor
    . intro c
      have hab := h c
      exact hab.left
    . intro c
      have hab := h c
      exact hab.right
  . intro h
    intro hC
    constructor
    . have hA := h.left hC
      exact hA
    . have hB := h.right hC
      exact hB
