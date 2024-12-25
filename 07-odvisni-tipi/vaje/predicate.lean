variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    intro x
    intro P
    apply h
    apply Exists.intro x
    exact P
  . intro h
    intro ha
    match ha with
    | ⟨x, hx⟩ =>
      have g := h x
      apply g
      exact hx

example : (r → ∀ x, p x) ↔ (∀ x, r → p x) := by
  apply Iff.intro
  . intro h
    intro x
    intro hb
    have hc := h hb
    have hd := hc x
    exact hd
  . intro h
    intro ha
    intro x
    have hb := h x
    apply hb
    exact ha

example : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hl hr =>
      match hr with
      | ⟨x, hx⟩ =>
        apply Exists.intro x
        apply And.intro
        . exact hl
        . exact hx
  . intro h
    match h with
    | ⟨x, hx⟩ =>
      apply And.intro
      . exact hx.left
      . apply Exists.intro x
        exact hx.right

example : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) := by
  intro h
  intro x
  cases h with
  | inl ha =>
    apply Or.inl
    exact ha
  | inr hb =>
    have hx := hb x
    apply Or.inr
    exact hx


-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    have ha : ∃ x, ¬ p x := by
      apply byContradiction
      intro hb
      apply h
      intro x
      apply byContradiction
      intro px
      apply hb
      apply Exists.intro x
      exact px
    exact ha
  . intro h
    match h with
    | ⟨x, hx⟩ =>
      intro ha
      have hb := ha x
      contradiction

example : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) := by
  apply Iff.intro
  . intro h
    intro x
    -- have ha := em r
    cases h with
    | inl ha =>
      apply Or.inl
      exact ha
    | inr hb =>
      have hc := hb x
      apply Or.inr
      exact hc
  . intro h
    have lem := em r
    cases lem with
    | inl ha =>
      apply Or.inl
      exact ha
    | inr hb =>
      apply Or.inr
      intro x
      have hc := h x
      cases hc with
      | inl ha =>
        contradiction
      | inr hb =>
        exact hb
