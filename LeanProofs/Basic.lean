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
