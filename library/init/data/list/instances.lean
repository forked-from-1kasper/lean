/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic
import init.control

open list

universes u v

local attribute [simp] join list.ret

instance : monad list :=
{ pure := @list.ret, map := @list.map, bind := @list.bind }

instance : alternative list :=
{ failure := @list.nil,
  orelse  := @list.append,
  ..list.monad }

namespace list

variables {α β : Type u} (p : α → Kan 0) [decidable_pred p]

instance bin_tree_to_list : has_coe (bin_tree α) (list α) :=
⟨bin_tree.to_list⟩

end list
