
section definitions

variable E : Type

private def ge_refl [H : partial_order E] (x : E) : ge x x := le_refl x

private def le_op_trans [H : partial_order E] (a b c : E) (ab : ge a b) (bc : ge b c) : ge a c := le_trans bc ab

def Op [partial_order E] : partial_order E :=
{ le := ge
, le_refl := le_refl
, le_trans := λ a b c a_ge_b b_ge_c, le_trans b_ge_c a_ge_b
, le_antisymm := λ a b a_ge_b b_ge_a, le_antisymm b_ge_a a_ge_b
}

variables {E}
variables (S T : set E)

def upper_bounds_of [partial_order E] : set E := λ x, ∀ y ∈ S, y ≤ x
def lower_bounds_of [partial_order E] : set E := λ x, ∀ y ∈ S, y ≥ x
def is_max_ [partial_order E] : set E := λ x, (x ∈ upper_bounds_of S) ∧ x ∈ S
def is_min_ [partial_order E] : set E := λ x, (x ∈ lower_bounds_of S) ∧ x ∈ S
notation x `is_max_of` S := is_max_ S x
notation x `is_min_of` S := is_min_ S x

def is_join [partial_order E] : set E := λ x, x is_min_of (upper_bounds_of S)
def is_meet [partial_order E] : set E := λ x, x is_max_of (lower_bounds_of S)

end definitions