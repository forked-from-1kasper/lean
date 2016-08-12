--
namespace foo
definition subsingleton (A : Type) := ∀⦃a b : A⦄, a = b
attribute subsingleton [class]

protected definition prop.subsingleton [instance] (P : Prop) : subsingleton P :=
λa b, proof_irrel _ _
end foo
