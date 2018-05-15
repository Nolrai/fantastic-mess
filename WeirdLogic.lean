
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

section definitions2
variables {E}
variables (S T : set E)

def upper_bounds_of [partial_order E] : set E := λ x, ∀ y ∈ S, y ≤ x
def lower_bounds_of [partial_order E] : set E := λ x, ∀ y ∈ S, y ≥ x
def is_max [partial_order E] : set E := λ x, (x ∈ upper_bounds_of S) ∧ x ∈ S
def is_min [partial_order E] : set E := λ x, (x ∈ lower_bounds_of S) ∧ x ∈ S
notation S `max_is` x := is_max S x
notation S `min_is` x := is_min S x

def is_join [partial_order E] : set E := λ x, (upper_bounds_of S) min_is x
def is_meet [partial_order E] : set E := λ x, (lower_bounds_of S) min_is x
end definitions2

def upair (x y : E) : set E := λ s, s = x ∨ s = y

class lattice E extends partial_order E :=
(top : E)
(bottom : E)

(join : E -> E -> E)
(meet : E -> E -> E)

(top_spec : is_meet ∅ top)
(bottom_spec : is_join ∅ top)

(join_spec : )


end definitions2

end definitions