import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NthRewrite

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

theorem prop_1_2_alt2 : 2 = Nat.succ (Nat.succ 0) := by
  rw [← one_eq_succ_zero] -- rewrite succ 0 as 1; goal becomes 2 = succ 1
  -- closed by rw's automatic rfl (since 2 is definitionally succ 1)

theorem prop_1_2_alt3 : 2 = Nat.succ (Nat.succ 0) := by
  rewrite [← one_eq_succ_zero] -- rewrite succ 0 as 1; goal becomes 2 = succ 1
  rewrite [← two_eq_succ_one] -- rewrite succ 1 as 2; goal becomes 2 = 2
  rfl -- closed by rfl

-- Proposition 1.3

theorem prop_1_3 (a b c : ℕ) : a + (b+0) + (c+0) = a + b + c := by
  rw [Nat.add_zero] -- rewrite b+0 as b; goal becomes a + b + (c+0) = a + b + c
  rw [Nat.add_zero] -- rewrite c+0 as c; goal becomes a + b + c = a + b + c
  -- closed by rfl automatically

-- Proposition 1.4

theorem prop_1_4 (n : ℕ) : Nat.succ n = n + 1 := by
  rfl -- closed by rfl automatically since `n + 1` and `Nat.succ n` are definitionally equal

theorem prop_1_4alt (n : ℕ) : Nat.succ n = n + 1 := by
  rewrite [one_eq_succ_zero] -- rewrite 1 as succ 0; goal becomes succ n = n + succ 0
  rewrite [Nat.add_succ] -- rewrite n + succ 0 as succ (n + 0); goal becomes succ n = succ (n + 0)
  rewrite [Nat.add_zero] -- rewrite n + 0 as n; goal becomes succ n = succ n
  rfl -- closed by rfl

-- Proposition 1.5

theorem three_eq_succ_two : 3 = Nat.succ 2 := rfl
theorem four_eq_succ_three : 4 = Nat.succ 3 := rfl

theorem prop_1_5 : 2 + 2 = 4 := by
  rw [four_eq_succ_three] -- rewrite 4 as succ 3; goal becomes 2 + 2 = succ 3
  -- closed by rfl automatically since 2 + 2 is definitionally succ 3

theorem prop_1_5_alt : 2 + 2 = 4 := by
  rewrite [four_eq_succ_three] -- rewrite 4 as succ 3; goal becomes 2 + 2 = succ 3
  rewrite [three_eq_succ_two] -- rewrite 3 as succ 2; goal becomes 2 + 2 = succ succ 2
  nth_rewrite 2 [two_eq_succ_one] -- rewrite the second 2 as succ 1;
                                  -- goal becomes 2 + succ 1 = succ succ 2
  rewrite[Nat.add_succ] -- rewrite 2 + succ 1 as succ (2 + 1);
                         -- goal becomes succ (2 + 1) = succ (succ 2)
  nth_rewrite 1 [← Nat.succ_eq_add_one] -- rewrite 2 + 1 as succ 2;
                                     -- goal becomes succ (succ 2) = succ (succ 2)
  rfl -- closed by rfl

-- -------------------------------------------------------
-- Addition World
-- -------------------------------------------------------

-- Proposition 2.1

theorem prop_2_1 (n : ℕ) : 0 + n = n := by
  induction n with -- This is the induction statement.
    | zero => -- This is the base case. The goal is 0 + 0 = 0.
      rw [Nat.add_zero] -- rewrite 0 + 0 as 0; goal becomes 0 = 0
      -- closed by rfl automatically
    | succ d ih => -- This is the induction step.
                   -- The goal is 0 + succ d = succ d given that 0 + d = d (ih).
      rw [Nat.add_succ] -- rewrite 0 + succ d as succ (0 + d); goal becomes succ (0 + d) = succ d
      rw [ih] -- rewrite 0 + d as d; goal becomes succ d = succ d
      -- closed by rfl automatically

-- Proposition 2.2

theorem prop_2_2 (a b : ℕ) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with -- This is the induction statement.
  | zero => -- This is the base case. The goal is succ a + 0 = succ (a + 0).
    rw [Nat.add_zero] -- rewrite succ a + 0 as succ a and a + 0 as a;
                      -- goal becomes succ a = succ a
    -- closed by rfl automatically
  | succ d ih => -- This is the induction step.
                 -- The goal is succ a + succ d = succ (a + succ d) given that
                 --succ a + d = succ (a + d) (ih).
    rw [Nat.add_succ] -- rewrite succ a + succ d as succ (succ a + d);
                      -- goal becomes succ (succ a + d) = succ (a + succ d)
    rw [Nat.add_succ] -- rewrite a + succ d as succ (a + d);
                      -- goal becomes succ (succ a + d) = succ (succ (a + d))
    rw [ih] -- rewrite succ a + d as succ (a + d);
           -- goal becomes succ (succ (a + d)) = succ (succ (a + d))
    -- closed by rfl automatically

theorem prop_2_2_alt (a b : ℕ) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with -- This is the induction statement.
  | zero => -- This is the base case. The goal is succ a + 0 = succ (a + 0).
    rewrite [Nat.add_zero] -- rewrite succ a + 0 as succ a;
                           -- goal becomes succ a = succ (a + 0)
    rewrite [Nat.add_zero] -- rewrite a + 0 as a;
                           -- goal becomes succ a = succ a
    rfl -- closed by rfl automatically
  | succ d ih => -- This is the induction step.
                 -- The goal is succ a + succ d = succ (a + succ d) given that
                 -- succ a + d = succ (a + d) (ih).
    rewrite [Nat.add_succ] -- rewrite succ a + succ d as succ (succ a + d);
                           -- goal becomes succ (succ a + d) = succ (a + succ d)
    rewrite [Nat.add_succ] -- rewrite a + succ d as succ (a + d);
                           -- goal becomes succ (succ a + d) = succ (succ (a + d))
    rewrite [ih] -- rewrite succ a + d as succ (a + d);
                 -- goal becomes succ (succ (a + d)) = succ (succ (a + d))
    rfl -- closed by rfl

-- Proposition 2.3

theorem prop_2_3 (a b : ℕ) : a + b = b + a := by
  induction b with -- This is the induction statement.
  | zero => -- This is the base case. The goal is a + 0 = 0 + a.
    rw [Nat.zero_add] -- rewrite 0 + a as a;
                           -- goal becomes a + 0 = a
    rw [Nat.add_zero] -- rewrite a + 0 as a;
                           -- goal becomes a = a
    -- closed by rfl automatically
  | succ d ih => -- This is the induction step.
                 -- The goal is a + succ d = succ d + a given that
                 -- a + d = d + a (ih).
    rw [Nat.add_succ] -- rewrite a + succ d as succ (a + d);
                           -- goal becomes succ (a + d) = succ d + a
    rw [Nat.succ_add] -- rewrite succ d + a as succ (d + a);
                           -- goal becomes succ (a + d) = succ (d + a)
    rw [ih] -- rewrite a + d as d + a;
                           -- goal becomes succ (d + a) = succ (d + a)
    -- closed by rfl automatically

theorem prop_2_3_alt (a b : ℕ) : a + b = b + a := by
  induction b with -- This is the induction statement.
  | zero => -- This is the base case. The goal is a + 0 = 0 + a.
    rewrite [Nat.zero_add] -- rewrite 0 + a as a;
                           -- goal becomes a + 0 = a
    rewrite [Nat.add_zero] -- rewrite a + 0 as a;
                           -- goal becomes a = a
    rfl -- closed by rfl automatically
  | succ d ih => -- This is the induction step.
                 -- The goal is a + succ d = succ d + a given that
                 -- a + d = d + a (ih).
    rewrite [Nat.add_succ] -- rewrite a + succ d as succ (a + d);
                           -- goal becomes succ (a + d) = succ d + a
    rewrite [Nat.succ_add] -- rewrite succ d + a as succ (d + a);
                           -- goal becomes succ (a + d) = succ (d + a)
    rewrite [ih] -- rewrite a + d as d + a;
                           -- goal becomes succ (d + a) = succ (d + a)
    rfl -- closed by rfl automatically



end NNG
