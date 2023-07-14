import data.real.basic
import data.vector
import algebra.module
open real
open_locale classical

theorem exists_integer_gt (x : ℝ) : ∃ (n : ℤ), ↑n > x :=
begin
    by_contradiction h,
  have hx : ∀ (n : ℤ), ↑n ≤ x,
  {
    intro n,
    by_contradiction hn,
    push_neg at h,
    have : ↑n > x,
    {
      rw not_le at hn,
      exact hn,
    },
    specialize h n,
    linarith,
  },
  let y := x + 1,
  have hy : y > x,
  simp [y],
  specialize hx ⌈y⌉,
  have h₁ : ↑⌈y⌉ ≤ x,
  {
    exact hx,
  },
  have h₂ : ↑⌈y⌉ > x,
  {
    have : y ≤ ⌈y⌉,
    {
      exact int.le_ceil y,
    },
    exact lt_of_lt_of_le hy this,
  },
  linarith,


end




variables {F : Type*} [field F]

class vector_space (F : Type*) (V : Type*) [field F] [add_comm_group V] extends module F V

variables {V : Type*} [add_comm_group V] [vector_space F V]

def linear_combination (s : finset V) (c : V → F) : V :=
  finset.sum s (λ v, (c v) • v )

def span (vectors : list V) : set V :=
  { v : V | ∃ (coeffs : V → F) (s : finset V), s ⊆ vectors.to_finset ∧ v = linear_combination s coeffs }

def empty_span : set V :=
  { 0 }


instance has_one_V : has_one V := ⟨0⟩
noncomputable def example_usage : V :=
  let s : finset V := {1, 2, 3} in
  let c : V → F := λ v, if v = 1 then 2 else if v = 2 then 3 else 1 in
  linear_combination s c

def span (s : finset V) : submodule F V :=
{
  carrier := { v : V | ∃ (c : V → F), v = linear_combination s c },
  zero_mem' := ⟨λ v, 0, by simp⟩,
  add_mem' := λ x y ⟨cx, hx⟩ ⟨cy, hy⟩, ⟨λ v, cx v + cy v, by simp_rw [linear_combination, hx, hy, pi.add_apply]⟩,
  smul_mem' := λ r x ⟨c, hx⟩, ⟨λ v, r * c v, by simp_rw [linear_combination, hx, smul_eq_mul, pi.smul_apply]⟩
}

--def linear_combination (s : finset β) (f : β → α) : β :=
--  finset.sum s (λ b, f b • b)

--import linear_algebra.basic

-- variables {α β : Type}
-- variables [ring α] [add_comm_group β] [module α β]
