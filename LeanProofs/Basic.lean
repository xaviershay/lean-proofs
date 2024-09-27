import Lean
import Mathlib
import Mathlib.Algebra.Divisibility.Basic

example {n : ℤ} : (2 ∣ n ^ 3 + 11 * n) := by
  have h : n ^ 3 + 11 * n = n * (n * n + 11) := by linarith
  rw [h]
  cases Int.even_or_odd n with
  | inl he =>
      obtain ⟨k, hk⟩ := he
      rw [hk]
      have p:   (k + k) * ((k + k) * (k + k) + 11)
              = 2 * (k * ((k + k) ^ 2 + 11)) := by linarith
      rw [p]
      exact dvd_mul_right 2 _
  | inr ho =>
      obtain ⟨k, hk⟩ := ho
      rw [hk]
      have p:   (2 * k + 1) * ((2 * k + 1) * (2 * k + 1) + 11)
              = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 14 * k + 6) := by linarith
      rw [p]
      exact dvd_mul_right 2 _

example {n : ℕ} : (3 ∣ n ^ 3 + 11 * n) := by
  induction n with
  | zero => exact dvd_zero 3
  | succ k ih =>
    have q:   (k + 1) ^ 3 + 11 * (k + 1)
            = k ^ 3 + 11 * k + 3 * k^2 + 3 * k + 12 := by linarith
    rw [q]
    rw [← Nat.dvd_add_iff_right]
    exact Nat.dvd_of_mod_eq_zero rfl
    rw [← Nat.dvd_add_iff_right]
    exact Nat.dvd_mul_right 3 k
    rw [← Nat.dvd_add_iff_right]
    exact Nat.dvd_mul_right 3 (k ^ 2)
    exact ih
