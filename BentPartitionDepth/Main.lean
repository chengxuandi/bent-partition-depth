import BentPartitionDepth.DoubleCounting
import BentPartitionDepth.WalshDerivative

/-!
# Bent partition depth theorem

This module connects Walsh flatness, balanced nonzero derivatives, finite double counting,
and the prime-power divisor lemma.
-/

namespace BentPartitionDepth

/-- Every bent partition depth is a positive power of the output prime, with exponent at
most the ambient dimension. -/
theorem bent_partition_depth {p n K : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hdiv : p ∣ K) (P : BlockPartition p n K)
    (hP : IsBentPartition P) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ K = p ^ k := by
  let hp : p.Prime := Fact.out
  apply prime_power_depth_of_derivative_zero_count hp hn hdiv P
  intro ell a ha
  exact derivative_zero_count_of_isBent hp hn (hP ell.1 ell.2) ha

end BentPartitionDepth
