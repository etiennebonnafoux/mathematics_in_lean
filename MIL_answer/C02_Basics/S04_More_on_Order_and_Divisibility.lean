import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    apply le_max_right
    apply le_max_left
  · show max b a ≤ max a b
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  apply le_min
  repeat
    apply le_trans (min_le_left (min a b) c)
    apply min_le_left
  apply le_min
  apply le_trans (min_le_left (min a b) c)
  apply min_le_right
  apply min_le_right
  apply le_min
  apply le_min
  apply min_le_left
  apply le_trans (min_le_right a (min b c))
  apply min_le_left
  apply le_trans (min_le_right a (min b c))
  apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  apply add_le_add_right
  apply min_le_left
  apply add_le_add_right
  apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  have le_min_add {x y z w : ℝ} : w ≤ x + z → w ≤ y + z → w ≤ min x y + z := by
    rw [ ← sub_le_iff_le_add, ← sub_le_iff_le_add,← sub_le_iff_le_add]
    exact le_min
  apply le_min_add
  apply min_le_left
  apply min_le_right

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  nth_rewrite 1 [← add_zero a,← add_neg_cancel b,add_comm b ,← add_assoc,← sub_eq_add_neg]
  rw [sub_le_iff_le_add]
  exact abs_add (a - b) b

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  · show x ∣ y * (x * z)
    rw [mul_comm,mul_assoc]
    apply dvd_mul_right
  · show  x ∣ x ^ 2
    apply dvd_mul_left
  · show x ∣ w ^ 2
    rw [pow_two]
    apply dvd_mul_of_dvd_left h

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply gcd_comm
  -- apply dvd_antisymm
  -- apply gcd_
end
