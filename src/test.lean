import data.real.basic
open real
open_locale classical

theorem exists_integ3er_gt (x : ℝ) : ∃ (n : ℤ), ↑n > x :=
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