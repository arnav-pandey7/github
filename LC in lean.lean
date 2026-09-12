import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic

theorem prime_gap {p q : ℕ} (hp : Nat.Prime p)
(hq : Nat.Prime q) (hp3 : 3 ≤ p) (h1 : p < q) : p + 2 ≤ q := by
  have h1 := hp.eq_two_or_odd
  have h2 := hq.eq_two_or_odd
  omega

def sieve_next_density (density : ℚ) (prime : ℕ) : ℚ :=
  density * (1 - 1 / (prime : ℚ))

theorem sieve_base_case_2 : 1 / (2 : ℚ) ≤ 1 - 1 / 2 := by
  norm_num

theorem sieve_step_2_to_3 (survival : ℚ) (hR : 1 / (2 : ℚ) ≤ survival) :
  1 / (3 : ℚ) ≤ survival * (1 - 1 / (3 : ℚ)) := by
  have hfactor : 0 ≤ 1 - 1 / (3 : ℚ) := by norm_num
  have hstep : 1 / (3 : ℚ) ≤ (1 / (2 : ℚ)) * (1 - 1 / (3 : ℚ)) := by norm_num
  exact hstep.trans (mul_le_mul_of_nonneg_right hR hfactor)

theorem sieve_step (q p : ℕ) (survival : ℚ) (hp3 : 3 ≤ (p : ℚ)) --Changing theorem prime_gap to h0.
(h0 : (p : ℚ) + 2 ≤ (q : ℚ)) (hR : 1 / (p : ℚ) ≤ survival) :
    1 / (q : ℚ) ≤ survival * (1 - 1 / (q : ℚ)) := by
  have hp0 : 0 < (p : ℚ) := by linarith
  have hq0 : 0 < (q : ℚ) := by linarith
  have hfactor : 0 ≤ 1 - 1 / (q : ℚ) := by
    rw [le_sub_iff_add_le, zero_add]
    rw [div_le_iff₀ hq0]
    linarith
  have hstep : 1 / (q : ℚ) ≤ (1 / (p : ℚ)) * (1 - 1 / (q : ℚ)) := by
    have h_eq : (1 / (p : ℚ)) * (1 - 1 / (q : ℚ)) = ((q : ℚ) - 1) / ((p : ℚ) * (q : ℚ)) := by
      field_simp
    rw [h_eq, div_le_div_iff₀ hq0 (mul_pos hp0 hq0)]
    nlinarith
  exact hstep.trans (mul_le_mul_of_nonneg_right hR hfactor)

def crossesOut (q m : ℕ) : Prop :=
  q ^ 2 ≤ m ∧ q ∣ m

theorem sieve_starts_at_square (q : ℕ) :
    crossesOut q (q ^ 2) := by
  constructor
  · exact le_rfl
  · exact dvd_pow_self q (by norm_num)

-- Just to show that the survival gets to be changed from q^2 and then,
-- New probability to get the remainings after the sieving becomes ≥ 1/q.
-- SOME THINGS TO BE MODIFIED AND DEFINED, IN 25% PHASE...

variable (n : ℕ)
-- Let p be a prime number less than or equal to n
variable (q : ℕ) (hp : Nat.Prime q) (h : q ≤ n)
-- Hypothesis: p is the NEAREST prime below n
-- (Meaning if any number 'q' is strictly between p and n, 'q' cannot be prime)
variable (h_nearest : ∀ p, q < p → p ≤ n → ¬ Nat.Prime p)

lemma prob_conversion_updated (q n : ℝ) (hq3 : 3 ≤ q) (h : q ≤ n) : 1 / q ≥ 1 / n := by
  have hq : 0 < q := by linarith
  have hn : 0 < n := by linarith
  -- Apply the same division inequality lemma
  exact (one_div_le_one_div hn hq).mpr h -- Just to convert ≥ 1/q to ≥ 1/n for future proofs.

-- Convert q(from previous theorems) to p(for future theorems),
-- To avoid confusion with the variable 'p' in the next theorem.


open Finset
/--
Legendre's Conjecture derived from the density sure:
The number of primes divided by the interval width is at least 1/n.
Since,from n^2 or p^2 to any square number of the very next prime number,
means until the next prime number square comes, the survival remains the same as 1/n.
-/
theorem legendres_conjecture_from_density_sure
    (n : ℕ) (hn : n ≥ 3) (_h55 : p = q)--Converting q to p, to avoid confusion with the variable.
    (h_density : ((filter Nat.Prime (Ioo (n ^ 2) ((n + 1) ^ 2))).card : ℚ)
    / ((n + 1) ^ 2 - n ^ 2) ≥ 1 / (n : ℚ)) : ∃ p : ℕ,
    Nat.Prime p ∧ n^2 < p ∧ p < (n + 1)^2 := by
  -- 1. Establish that the difference between consecutive squares is 2n + 1
  have h_diff : ((n + 1)^2 - n^2 : ℚ) = 2 * (n : ℚ) + 1 := by
    ring
  -- Substitute the difference into our density
  rw [h_diff] at h_density
  -- 2. Ensure denominators are positive and non-zero (since n ≥ 3)
  have hn_pos : (n : ℚ) > 0 := by positivity
  have h_denom_pos : 2 * (n : ℚ) + 1 > 0 := by positivity
  have hn_nz : (n : ℚ) ≠ 0 := ne_of_gt hn_pos
  have h_denom_nz : 2 * (n : ℚ) + 1 ≠ 0 := ne_of_gt h_denom_pos
  -- 3. Calculate expected number of primes by clearing the denominators via field_simp
  have h_card : ((filter Nat.Prime (Ioo (n^2) ((n + 1)^2))).card : ℚ)
   ≥ (2 * (n : ℚ) + 1) / (n : ℚ) := by
    rw [ge_iff_le] at h_density ⊢
    -- field_simp clears fractions when given non-zero proofs for the denominators
    field_simp [hn_nz, h_denom_nz] at h_density ⊢
    linarith
  -- 4. Since 2 + 1/n > 0, the rational cardinality is strictly greater than 0
  have h_card_pos : ((filter Nat.Prime (Ioo (n^2) ((n + 1)^2))).card : ℚ) > 0 := by
    have h_frac_pos : (2 * (n : ℚ) + 1) / (n : ℚ) > 0 := by positivity
    linarith
  -- 5. Cast back to natural numbers
  have h_card_nat_pos : (filter Nat.Prime (Ioo (n^2) ((n + 1)^2))).card > 0 := by
    exact_mod_cast h_card_pos
  -- 6. Extract the prime number from the non-empty Finset
  rcases card_pos.mp h_card_nat_pos with ⟨p, hp⟩
  rw [mem_filter, mem_Ioo] at hp
  use p
  exact ⟨hp.2, hp.1.1, hp.1.2⟩
