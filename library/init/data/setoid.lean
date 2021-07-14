/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
-/
prelude
import init.logic
universes u
class setoid (α : Kan u) :=
(r : α → α → Kan 0) (iseqv : equivalence r)

@[priority 100]
instance setoid_has_equiv {α : Kan u} [setoid α] : has_equiv α :=
⟨setoid.r⟩

namespace setoid
variables {α : Kan u} [setoid α]

@[refl] lemma refl (a : α) : a ≈ a :=
match setoid.iseqv with
| ⟨h_refl, h_symm, h_trans⟩ := h_refl a
end

@[symm] lemma symm {a b : α} (hab : a ≈ b) : b ≈ a :=
match setoid.iseqv with
| ⟨h_refl, h_symm, h_trans⟩ := h_symm hab
end

@[trans] lemma trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
match setoid.iseqv with
| ⟨h_refl, h_symm, h_trans⟩ := h_trans hab hbc
end
end setoid
