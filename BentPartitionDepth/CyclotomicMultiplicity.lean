import BentPartitionDepth.Definitions

namespace BentPartitionDepth

open scoped BigOperators
open Finset

/-- For a prime number of output values, a vanishing root-of-unity sum with natural
multiplicities has all multiplicities equal. -/
theorem prime_root_sum_multiplicities_equal {p : ℕ} (hp : p.Prime)
    (m : Fin p → ℕ)
    (hzero : ∑ c : Fin p, (m c : ℂ) * omega p ^ c.val = 0) :
    ∀ c d, m c = m d := by
  have hprim : IsPrimitiveRoot (omega p) p := omega_isPrimitiveRoot hp.ne_zero
  have hz : ∀ c d, (m c : ℤ) = (m d : ℤ) :=
    (hprim.sum_eq_zero_iff_forall_eq_int hp (fun c ↦ (m c : ℤ))).mp (by
      simpa using hzero)
  intro c d
  exact_mod_cast hz c d

/-- If the multiplicities additionally sum to `p^n`, each one is `p^(n-1)`. -/
theorem prime_root_sum_multiplicity_eq_pow {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (m : Fin p → ℕ)
    (hzero : ∑ c : Fin p, (m c : ℂ) * omega p ^ c.val = 0)
    (hsum : ∑ c : Fin p, m c = p ^ n) :
    ∀ c, m c = p ^ (n - 1) := by
  have hall := prime_root_sum_multiplicities_equal hp m hzero
  intro c
  have hconst : ∑ d : Fin p, m d = p * m c := by
    calc
      (∑ d : Fin p, m d) = ∑ _d : Fin p, m c := by
        apply Finset.sum_congr rfl
        intro d _
        exact hall d c
      _ = p * m c := by simp
  have hmul : p * m c = p * p ^ (n - 1) := by
    rw [← hconst, hsum]
    cases n with
    | zero => omega
    | succ k => simp [pow_succ, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hp.pos hmul

end BentPartitionDepth
