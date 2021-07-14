/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core init.logic init.control init.data.basic init.version
import init.control.combinators init.function
import init.util init.coe init.wf init.meta init.data
import init.meta.float

@[user_attribute]
meta def debugger.attr : user_attribute :=
{ name  := `breakpoint,
  descr := "breakpoint for debugger" }
