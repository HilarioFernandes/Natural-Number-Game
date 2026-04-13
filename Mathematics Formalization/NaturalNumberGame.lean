import Mathlib

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









end NNG
