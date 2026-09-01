# Bent Partition Depth

This repository contains a Lean 4 formalization and a self-contained LaTeX proof of the following result: the depth of a bent partition over `F_p^n` is a power of the prime characteristic `p`.

The machine-checked theorem is:

```lean
theorem bent_partition_depth {p n K : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hdiv : p ∣ K) (P : BlockPartition p n K)
    (hP : IsBentPartition P) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ K = p ^ k
```

Here `IsBentPartition P` quantifies over every balanced labeling of the blocks. No regularity, weak regularity, dual-bent, spread, or equal-block-size assumption is used.

The proof follows the chain

```text
bent
  -> every nonzero derivative is balanced
  -> average over all balanced block labelings
  -> K * T_a = p^n
  -> K divides p^n
  -> K = p^k.
```

## Verification

The project is pinned to Lean `v4.33.0` and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

With Lake available, run:

```shell
lake build
```

The root module is [`BentPartitionDepth.lean`](BentPartitionDepth.lean). The main theorem is in [`BentPartitionDepth/Main.lean`](BentPartitionDepth/Main.lean), and the written proof is available as [LaTeX](paper/bent_partition_depth_proof.tex) and [PDF](paper/bent_partition_depth_proof.pdf).

## Repository contents

- `BentPartitionDepth/Definitions.lean`: partitions, balanced labelings, and bentness.
- `BentPartitionDepth/CyclotomicMultiplicity.lean`: the prime cyclotomic multiplicity argument.
- `BentPartitionDepth/WalshDerivative.lean`: Walsh flatness and balanced derivatives.
- `BentPartitionDepth/DoubleCounting.lean`: balanced-labeling averaging and divisibility.
- `BentPartitionDepth/Main.lean`: the final depth theorem.
- `paper/`: the complete mathematical proof.

No license is included.
