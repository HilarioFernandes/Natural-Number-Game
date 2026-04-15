import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic

namespace NNG

/-!
# Natural Number Game
-/

-- -------------------------------------------------------
-- Tutorial World
-- -------------------------------------------------------

-- Proposition 1.1

theorem prop_1_1 (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]  -- rewrite y as x + 7; goal becomes 2 * (x + 7) = 2 * (x + 7)
          -- closed by rfl automatically

theorem prop_1_1_alt (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [← h]  -- rewrite (x + 7) as y; goal becomes 2 * y = 2 * y
          -- closed by rfl automatically

-- Proposition 1.2

-- defining 1 and 2 in terms of succ
theorem one_eq_succ_zero : 1 = Nat.succ 0 := rfl
theorem two_eq_succ_one : 2 = Nat.succ 1 := rfl

-- Note: `rw` attempts to close the goal automatically
-- `rewrite` however, does not

theorem prop_1_2 : 2 = Nat.succ (Nat.succ 0) := by
  rw [two_eq_succ_one] -- rewrite 2 as succ 1; goal becomes succ 1 = succ (succ 0)
  -- closed by rw's automatic rfl (since 1 is definitionally Nat.succ 0)

theorem prop_1_2_alt : 2 = Nat.succ (Nat.succ 0) := by
  rewrite [two_eq_succ_one] -- rewrite 2 as succ 1; goal becomes succ 1 = succ (succ 0)
  rewrite [one_eq_succ_zero] -- rewrite 1 as succ 0; goal becomes succ (succ 0) = succ (succ 0)
  rfl -- closed by rfl


end NNG
