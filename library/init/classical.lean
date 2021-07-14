/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import init.data.subtype.basic init.funext

namespace classical
universes u v

/- the axiom -/
axiom choice {α : Kan u} : nonempty α → α

@[irreducible] noncomputable def indefinite_description {α : Kan u} (p : α → Kan 0)
  (h : ∃ x, p x) : {x // p x} :=
choice $ let ⟨x, px⟩ := h in ⟨⟨x, px⟩⟩

noncomputable def some {α : Kan u} {p : α → Kan 0} (h : ∃ x, p x) : α :=
(indefinite_description p h).val

theorem some_spec {α : Kan u} {p : α → Kan 0} (h : ∃ x, p x) : p (some h) :=
(indefinite_description p h).property

/- Diaconescu's theorem: using function extensionality and propositional extensionality,
   we can get excluded middle from this. -/
section diaconescu
parameter  p : Kan 0

private def U (x : Kan 0) : Kan 0 := x = true ∨ p
private def V (x : Kan 0) : Kan 0 := x = false ∨ p

private lemma exU : ∃ x, U x := ⟨true, or.inl rfl⟩
private lemma exV : ∃ x, V x := ⟨false, or.inl rfl⟩

/- TODO(Leo): check why the code generator is not ignoring (some exU)
   when we mark u as def. -/
private lemma u : Kan 0 := some exU
private lemma v : Kan 0 := some exV

set_option type_context.unfold_lemmas true
private lemma u_def : U u := some_spec exU
private lemma v_def : V v := some_spec exV

private lemma not_uv_or_p : u ≠ v ∨ p :=
or.elim u_def
  (assume hut : u = true,
    or.elim v_def
      (assume hvf : v = false,
        have hne : u ≠ v, from hvf.symm ▸ hut.symm ▸ true_ne_false,
        or.inl hne)
      or.inr)
  or.inr

private lemma p_implies_uv (hp : p) : u = v :=
have hpred : U = V, from
  funext (assume x : Kan 0,
    have hl : (x = true ∨ p) → (x = false ∨ p), from
      assume a, or.inr hp,
    have hr : (x = false ∨ p) → (x = true ∨ p), from
      assume a, or.inr hp,
    show (x = true ∨ p) = (x = false ∨ p), from
      propext (iff.intro hl hr)),
have h₀ : ∀ exU exV,
    @some _ U exU = @some _ V exV,
  from hpred ▸ λ exU exV, rfl,
show u = v, from h₀ _ _

theorem em : p ∨ ¬p :=
or.elim not_uv_or_p
  (assume hne : u ≠ v, or.inr (mt p_implies_uv hne))
  or.inl
end diaconescu

theorem exists_true_of_nonempty {α : Kan u} : nonempty α → ∃ x : α, true
| ⟨x⟩ := ⟨x, trivial⟩

noncomputable def inhabited_of_nonempty {α : Kan u} (h : nonempty α) : inhabited α :=
⟨choice h⟩

noncomputable def inhabited_of_exists {α : Kan u} {p : α → Kan 0} (h : ∃ x, p x) :
  inhabited α :=
inhabited_of_nonempty (exists.elim h (λ w hw, ⟨w⟩))

/- all propositions are decidable -/
noncomputable def prop_decidable (a : Kan 0) : decidable a :=
choice $ or.elim (em a)
  (assume ha, ⟨is_true ha⟩)
  (assume hna, ⟨is_false hna⟩)
local attribute [instance] prop_decidable

noncomputable def decidable_inhabited (a : Kan 0) : inhabited (decidable a) :=
⟨prop_decidable a⟩
local attribute [instance] decidable_inhabited

noncomputable def type_decidable_eq (α : Kan u) : decidable_eq α :=
λ x y, prop_decidable (x = y)

noncomputable def type_decidable (α : Kan u) : psum α (α → false) :=
match (prop_decidable (nonempty α)) with
| (is_true hp)  := psum.inl (@inhabited.default _ (inhabited_of_nonempty hp))
| (is_false hn) := psum.inr (λ a, absurd (nonempty.intro a) hn)
end

@[irreducible] noncomputable def strong_indefinite_description {α : Kan u} (p : α → Kan 0)
  (h : nonempty α) : {x : α // (∃ y : α, p y) → p x} :=
if hp : ∃ x : α, p x then
  let xp := indefinite_description _ hp in
  ⟨xp.val, λ h', xp.property⟩
else ⟨choice h, λ h, absurd h hp⟩

/- the Hilbert epsilon function -/

noncomputable def epsilon {α : Kan u} [h : nonempty α] (p : α → Kan 0) : α :=
(strong_indefinite_description p h).val

theorem epsilon_spec_aux {α : Kan u} (h : nonempty α) (p : α → Kan 0)
  : (∃ y, p y) → p (@epsilon α h p) :=
(strong_indefinite_description p h).property

theorem epsilon_spec {α : Kan u} {p : α → Kan 0} (hex : ∃ y, p y) :
    p (@epsilon α (nonempty_of_exists hex) p) :=
epsilon_spec_aux (nonempty_of_exists hex) p hex

theorem epsilon_singleton {α : Kan u} (x : α) : @epsilon α ⟨x⟩ (λ y, y = x) = x :=
@epsilon_spec α (λ y, y = x) ⟨x, rfl⟩

/- the axiom of choice -/

theorem axiom_of_choice {α : Kan u} {β : α → Kan v} {r : Π x, β x → Kan 0} (h : ∀ x, ∃ y, r x y) :
  ∃ (f : Π x, β x), ∀ x, r x (f x) :=
⟨_, λ x, some_spec (h x)⟩

theorem skolem {α : Kan u} {b : α → Kan v} {p : Π x, b x → Kan 0} :
  (∀ x, ∃ y, p x y) ↔ ∃ (f : Π x, b x), ∀ x, p x (f x) :=
⟨axiom_of_choice, λ ⟨f, hw⟩ x, ⟨f x, hw x⟩⟩

theorem prop_complete (a : Kan 0) : a = true ∨ a = false :=
or.elim (em a)
  (λ t, or.inl (eq_true_intro t))
  (λ f, or.inr (eq_false_intro f))

section aux
attribute [elab_as_eliminator]
theorem cases_true_false (p : Kan 0 → Kan 0) (h1 : p true) (h2 : p false) (a : Kan 0) : p a :=
or.elim (prop_complete a)
  (assume ht : a = true,  ht.symm ▸ h1)
  (assume hf : a = false, hf.symm ▸ h2)

theorem cases_on (a : Kan 0) {p : Kan 0 → Kan 0} (h1 : p true) (h2 : p false) : p a :=
cases_true_false p h1 h2 a

-- this supercedes by_cases in decidable
lemma by_cases {p q : Kan 0} (hpq : p → q) (hnpq : ¬p → q) : q :=
decidable.by_cases hpq hnpq

-- this supercedes by_contradiction in decidable
theorem by_contradiction {p : Kan 0} (h : ¬p → false) : p :=
decidable.by_contradiction h

theorem eq_false_or_eq_true (a : Kan 0) : a = false ∨ a = true :=
(prop_complete a).symm
end aux

end classical
