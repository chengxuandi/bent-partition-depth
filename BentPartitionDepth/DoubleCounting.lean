import BentPartitionDepth.Definitions

namespace BentPartitionDepth

open scoped BigOperators
open Finset

/-- The finite type of all balanced labelings of `K` block indices by `ZMod p`. -/
abbrev BalancedLabelingType (p K : ℕ) [NeZero p] :=
  {ell : Fin K → ZMod p // IsBalancedLabeling ell}

/-- A balanced labeling exists whenever `p ∣ K`.  It is obtained by identifying the
block indices with `ZMod p × Fin (K / p)` and projecting to the first coordinate. -/
noncomputable def canonicalBalancedLabeling {p K : ℕ} [NeZero p] (hdiv : p ∣ K) :
    BalancedLabelingType p K := by
  let e : Fin K ≃ ZMod p × Fin (K / p) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_prod, ZMod.card]
    exact (Nat.mul_div_cancel' hdiv).symm)
  refine ⟨fun i ↦ (e i).1, ?_⟩
  intro c
  let ec : {i : Fin K // (e i).1 = c} ≃ Fin (K / p) :=
    { toFun := fun i ↦ (e i.1).2
      invFun := fun s ↦ ⟨e.symm (c, s), by simp⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply e.injective
        simp only [Equiv.apply_symm_apply]
        exact Prod.ext i.2.symm rfl
      right_inv := by intro s; simp }
  simpa using Fintype.card_congr ec

lemma balancedLabelingType_card_pos {p K : ℕ} [NeZero p] (hdiv : p ∣ K) :
    0 < Nat.card (BalancedLabelingType p K) := by
  letI : Nonempty (BalancedLabelingType p K) := ⟨canonicalBalancedLabeling hdiv⟩
  exact Nat.card_pos

/-- Reindexing the blocks by a permutation preserves balancedness. -/
def reindexBalanced {p K : ℕ} [NeZero p] (σ : Equiv.Perm (Fin K))
    (ell : BalancedLabelingType p K) : BalancedLabelingType p K := by
  refine ⟨fun i ↦ ell.1 (σ i), ?_⟩
  intro c
  rw [← ell.2 c]
  apply Fintype.card_congr
  exact
    { toFun := fun i ↦ ⟨σ i.1, i.2⟩
      invFun := fun j ↦ ⟨σ.symm j.1, by simpa using j.2⟩
      left_inv := by intro i; ext; simp
      right_inv := by intro j; ext; simp }

/-- Reindexing by a permutation is an equivalence of balanced labelings. -/
def reindexBalancedEquiv {p K : ℕ} [NeZero p] (σ : Equiv.Perm (Fin K)) :
    BalancedLabelingType p K ≃ BalancedLabelingType p K where
  toFun := reindexBalanced σ
  invFun := reindexBalanced σ.symm
  left_inv := by intro ell; ext i; simp [reindexBalanced]
  right_inv := by intro ell; ext i; simp [reindexBalanced]

/-- Number of balanced labelings in which two fixed block indices receive the same label. -/
noncomputable def sameLabelCount {p K : ℕ} [NeZero p] (i j : Fin K) : ℕ :=
  Nat.card {ell : BalancedLabelingType p K // ell.1 i = ell.1 j}

/-- For fixed `i`, all distinct choices of the second index give the same count. -/
def sameLabelEquiv {p K : ℕ} [NeZero p] (i j k : Fin K)
    (hij : i ≠ j) (hik : i ≠ k) :
    {ell : BalancedLabelingType p K // ell.1 i = ell.1 j} ≃
      {ell : BalancedLabelingType p K // ell.1 i = ell.1 k} := by
  let σ : Equiv.Perm (Fin K) := Equiv.swap j k
  let E : BalancedLabelingType p K ≃ BalancedLabelingType p K :=
    reindexBalancedEquiv σ
  refine
    { toFun := fun ell ↦ ⟨E ell.1, ?_⟩
      invFun := fun ell ↦ ⟨E.symm ell.1, ?_⟩
      left_inv := by intro ell; apply Subtype.ext; exact E.left_inv ell.1
      right_inv := by intro ell; apply Subtype.ext; exact E.right_inv ell.1 }
  · change ell.1.1 (σ i) = ell.1.1 (σ k)
    rw [Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_right]
    exact ell.2
  · change ell.1.1 (σ.symm i) = ell.1.1 (σ.symm j)
    simpa [σ, Equiv.swap_apply_of_ne_of_ne hij hik] using ell.2

lemma sameLabelCount_eq {p K : ℕ} [NeZero p] (i j k : Fin K)
    (hij : i ≠ j) (hik : i ≠ k) :
    sameLabelCount (p := p) i j = sameLabelCount (p := p) i k := by
  exact Nat.card_congr (sameLabelEquiv i j k hij hik)

lemma card_same_label_except {p K : ℕ} [NeZero p]
    (ell : BalancedLabelingType p K) (i : Fin K) :
    Nat.card {j : Fin K // j ≠ i ∧ ell.1 j = ell.1 i} = K / p - 1 := by
  classical
  let fiber := {j : Fin K // ell.1 j = ell.1 i}
  let ii : fiber := ⟨i, rfl⟩
  let e : {j : Fin K // j ≠ i ∧ ell.1 j = ell.1 i} ≃ {j : fiber // j ≠ ii} :=
    { toFun := fun j ↦
        ⟨⟨j.1, j.2.2⟩, fun h ↦ j.2.1 (congrArg Subtype.val h)⟩
      invFun := fun j ↦
        ⟨j.1.1, ⟨fun h ↦ j.2 (Subtype.ext h), j.1.2⟩⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  have hcomp := Fintype.card_subtype_compl (fun j : fiber ↦ j = ii)
  have hone : Fintype.card {j : fiber // j = ii} = 1 := by simp
  rw [hone] at hcomp
  rw [hcomp, show Fintype.card fiber = K / p from ell.2 (ell.1 i)]

/-- Incidences `(ell,j)` where `j ≠ i` and `j` has the same label as `i`. -/
abbrev LabelIncidence (p K : ℕ) [NeZero p] (i : Fin K) :=
  Σ ell : BalancedLabelingType p K,
    {j : Fin K // j ≠ i ∧ ell.1 j = ell.1 i}

lemma labelIncidence_card_by_labeling {p K : ℕ} [NeZero p] (i : Fin K) :
    Nat.card (LabelIncidence p K i) =
      Nat.card (BalancedLabelingType p K) * (K / p - 1) := by
  classical
  letI := Fintype.ofFinite (BalancedLabelingType p K)
  rw [Nat.card_sigma]
  calc
    (∑ ell : BalancedLabelingType p K,
        Nat.card {j : Fin K // j ≠ i ∧ ell.1 j = ell.1 i}) =
        Fintype.card (BalancedLabelingType p K) * (K / p - 1) :=
      Finset.sum_const_nat (fun ell _ ↦ card_same_label_except ell i)
    _ = Nat.card (BalancedLabelingType p K) * (K / p - 1) := by
      rw [Nat.card_eq_fintype_card]

def labelIncidenceSwapEquiv {p K : ℕ} [NeZero p] (i : Fin K) :
    LabelIncidence p K i ≃
      Σ j : {j : Fin K // j ≠ i},
        {ell : BalancedLabelingType p K // ell.1 i = ell.1 j.1} where
  toFun q := ⟨⟨q.2.1, q.2.2.1⟩, ⟨q.1, q.2.2.2.symm⟩⟩
  invFun q := ⟨q.2.1, ⟨q.1.1, q.1.2, q.2.2.symm⟩⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl

lemma card_fin_ne (K : ℕ) (i : Fin K) : Nat.card {j : Fin K // j ≠ i} = K - 1 := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hcomp := Fintype.card_subtype_compl (fun j : Fin K ↦ j = i)
  have hone : Fintype.card {j : Fin K // j = i} = 1 := by simp
  rw [hone] at hcomp
  simpa using hcomp

/-- Cross-multiplied balanced-labeling probability:
`(K-1) * #same = (K/p-1) * #all`. -/
theorem balanced_labeling_pair_count {p K : ℕ} [NeZero p]
    (i j : Fin K) (hij : i ≠ j) :
    (K - 1) * sameLabelCount (p := p) i j =
      (K / p - 1) * Nat.card (BalancedLabelingType p K) := by
  classical
  letI := Fintype.ofFinite {j : Fin K // j ≠ i}
  have hswap := Nat.card_congr (labelIncidenceSwapEquiv (p := p) i)
  rw [labelIncidence_card_by_labeling] at hswap
  rw [Nat.card_sigma] at hswap
  have hterm (k : {k : Fin K // k ≠ i}) :
      Nat.card {ell : BalancedLabelingType p K // ell.1 i = ell.1 k.1} =
        sameLabelCount (p := p) i j := by
    change sameLabelCount (p := p) i k.1 = sameLabelCount (p := p) i j
    exact sameLabelCount_eq i k.1 j k.2.symm hij
  have hsum :
      (∑ k : {k : Fin K // k ≠ i},
        Nat.card {ell : BalancedLabelingType p K // ell.1 i = ell.1 k.1}) =
        Nat.card {k : Fin K // k ≠ i} * sameLabelCount (p := p) i j :=
    by
      simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using
        (Finset.sum_const_nat (s := Finset.univ) (fun k _ ↦ hterm k))
  rw [hsum, card_fin_ne] at hswap
  simpa [Nat.mul_comm] using hswap.symm

/-- Pairs consisting of a balanced labeling and a point at which the induced derivative
vanishes. -/
abbrev ZeroDerivativePairs {p n K : ℕ} [NeZero p]
    (P : BlockPartition p n K) (a : V p n) :=
  Σ ell : BalancedLabelingType p K,
    {x : V p n // derivative (induced P ell.1) a x = 0}

/-- The same finite set of zero-derivative pairs, with the two coordinates reversed. -/
def zeroDerivativePairsSwapEquiv {p n K : ℕ} [NeZero p]
    (P : BlockPartition p n K) (a : V p n) :
    ZeroDerivativePairs P a ≃
      Σ x : V p n,
        {ell : BalancedLabelingType p K // derivative (induced P ell.1) a x = 0} where
  toFun q := ⟨q.2.1, ⟨q.1, q.2.2⟩⟩
  invFun q := ⟨q.2.1, ⟨q.1, q.2.2⟩⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl

lemma zeroDerivativePairs_card_by_labeling {p n K : ℕ} [NeZero p]
    (P : BlockPartition p n K) (a : V p n)
    (hzero : ∀ ell : BalancedLabelingType p K,
      Fintype.card {x : V p n // derivative (induced P ell.1) a x = 0} = p ^ n / p) :
    Nat.card (ZeroDerivativePairs P a) =
      Nat.card (BalancedLabelingType p K) * (p ^ n / p) := by
  classical
  letI := Fintype.ofFinite (BalancedLabelingType p K)
  rw [Nat.card_sigma]
  calc
    (∑ ell : BalancedLabelingType p K,
        Nat.card {x : V p n // derivative (induced P ell.1) a x = 0}) =
        Fintype.card (BalancedLabelingType p K) * (p ^ n / p) := by
      apply Finset.sum_const_nat
      intro ell _
      rw [Nat.card_eq_fintype_card, hzero ell]
    _ = Nat.card (BalancedLabelingType p K) * (p ^ n / p) := by
      rw [Nat.card_eq_fintype_card]

lemma zeroDerivativeLabelings_card {p n K : ℕ} [NeZero p]
    (P : BlockPartition p n K) (a x : V p n) :
    Nat.card {ell : BalancedLabelingType p K //
        derivative (induced P ell.1) a x = 0} =
      if P.block x = P.block (x + a) then
        Nat.card (BalancedLabelingType p K)
      else sameLabelCount (p := p) (P.block x) (P.block (x + a)) := by
  classical
  by_cases hsame : P.block x = P.block (x + a)
  · rw [if_pos hsame]
    apply Nat.card_congr
    exact
      { toFun := fun ell ↦ ell.1
        invFun := fun ell ↦ ⟨ell, by simp [derivative, induced, hsame]⟩
        left_inv := by intro ell; rfl
        right_inv := by intro ell; rfl }
  · rw [if_neg hsame]
    apply Nat.card_congr
    exact
      { toFun := fun ell ↦ ⟨ell.1, by
          have hz := ell.2
          change ell.1.1 (P.block (x + a)) - ell.1.1 (P.block x) = 0 at hz
          exact (sub_eq_zero.mp hz).symm⟩
        invFun := fun ell ↦ ⟨ell.1, by
          change ell.1.1 (P.block (x + a)) - ell.1.1 (P.block x) = 0
          exact sub_eq_zero.mpr ell.2.symm⟩
        left_inv := by intro ell; rfl
        right_inv := by intro ell; rfl }

lemma sameBlockCount_le {p n K : ℕ} [NeZero p]
    (P : BlockPartition p n K) (a : V p n) : sameBlockCount P a ≤ p ^ n := by
  calc
    sameBlockCount P a ≤ Fintype.card (V p n) := by
      exact Fintype.card_subtype_le _
    _ = p ^ n := by simp [V]

/-- The zero-derivative pairs counted by points.  This is the finite, division-free
version of the balanced-labeling averaging identity. -/
lemma zeroDerivativePairs_weighted_card {p n K : ℕ} [NeZero p]
    (P : BlockPartition p n K) (a : V p n) :
    (K - 1) * Nat.card (ZeroDerivativePairs P a) =
      sameBlockCount P a * ((K - 1) * Nat.card (BalancedLabelingType p K)) +
      (p ^ n - sameBlockCount P a) *
        ((K / p - 1) * Nat.card (BalancedLabelingType p K)) := by
  classical
  letI := Fintype.ofFinite (BalancedLabelingType p K)
  let Q := p ^ n
  let L := Nat.card (BalancedLabelingType p K)
  let T := sameBlockCount P a
  have hswap : Nat.card (ZeroDerivativePairs P a) =
      ∑ x : V p n, Nat.card {ell : BalancedLabelingType p K //
        derivative (induced P ell.1) a x = 0} := by
    calc
      Nat.card (ZeroDerivativePairs P a) =
          Nat.card (Σ x : V p n,
            {ell : BalancedLabelingType p K //
              derivative (induced P ell.1) a x = 0}) :=
        Nat.card_congr (zeroDerivativePairsSwapEquiv P a)
      _ = ∑ x : V p n, Nat.card {ell : BalancedLabelingType p K //
            derivative (induced P ell.1) a x = 0} := Nat.card_sigma
  have hterm (x : V p n) :
      (K - 1) * Nat.card {ell : BalancedLabelingType p K //
          derivative (induced P ell.1) a x = 0} =
        if P.block x = P.block (x + a) then (K - 1) * L else (K / p - 1) * L := by
    rw [zeroDerivativeLabelings_card]
    split_ifs with hx
    · rfl
    · exact balanced_labeling_pair_count (P.block x) (P.block (x + a)) hx
  have hsame :
      #{x : V p n | P.block x = P.block (x + a)} = T := by
    rw [← Fintype.card_subtype]
    rfl
  have hsameCard :
      Fintype.card {x : V p n // P.block x = P.block (x + a)} = T := by
    rw [Fintype.card_subtype, hsame]
  have hdiff :
      #{x : V p n | ¬P.block x = P.block (x + a)} = Q - T := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl]
    rw [hsameCard]
    simp [Q, V]
  calc
    (K - 1) * Nat.card (ZeroDerivativePairs P a) =
        (K - 1) * ∑ x : V p n,
          Nat.card {ell : BalancedLabelingType p K //
            derivative (induced P ell.1) a x = 0} := by rw [hswap]
    _ = ∑ x : V p n, (K - 1) *
          Nat.card {ell : BalancedLabelingType p K //
            derivative (induced P ell.1) a x = 0} := by rw [Finset.mul_sum]
    _ = ∑ x : V p n,
          if P.block x = P.block (x + a) then (K - 1) * L else (K / p - 1) * L := by
      apply Finset.sum_congr rfl
      intro x _
      exact hterm x
    _ = T * ((K - 1) * L) + (Q - T) * ((K / p - 1) * L) := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, nsmul_eq_mul]
      simpa using congrArg₂ (fun u v : ℕ ↦ u * ((K - 1) * L) +
        v * ((K / p - 1) * L)) hsame hdiff
    _ = sameBlockCount P a * ((K - 1) * Nat.card (BalancedLabelingType p K)) +
        (p ^ n - sameBlockCount P a) *
          ((K / p - 1) * Nat.card (BalancedLabelingType p K)) := rfl

/-- The combinatorial core: if every balanced block labeling has exactly `p^n/p`
zeroes in the fixed derivative direction, then `K * T_a = p^n`. -/
theorem double_counting_identity {p n K : ℕ} [NeZero p]
    (hp : p.Prime) (hn : 0 < n) (hdiv : p ∣ K)
    (P : BlockPartition p n K) (a : V p n)
    (hzero : ∀ ell : BalancedLabelingType p K,
      Fintype.card {x : V p n // derivative (induced P ell.1) a x = 0} = p ^ n / p) :
    K * sameBlockCount P a = p ^ n := by
  let L := Nat.card (BalancedLabelingType p K)
  let T := sameBlockCount P a
  let Q := p ^ n
  have hcard := zeroDerivativePairs_card_by_labeling P a hzero
  have hweighted := zeroDerivativePairs_weighted_card P a
  have hwithL :
      L * ((K - 1) * (Q / p)) =
        L * (T * (K - 1) + (Q - T) * (K / p - 1)) := by
    calc
      L * ((K - 1) * (Q / p)) =
          (K - 1) * (L * (Q / p)) := by ring
      _ = (K - 1) * Nat.card (ZeroDerivativePairs P a) := by
        rw [hcard]
      _ = T * ((K - 1) * L) + (Q - T) * ((K / p - 1) * L) := by
        exact hweighted
      _ = L * (T * (K - 1) + (Q - T) * (K / p - 1)) := by ring
  have hLpos : 0 < L := balancedLabelingType_card_pos hdiv
  have havg :
      (K - 1) * (Q / p) = T * (K - 1) + (Q - T) * (K / p - 1) :=
    Nat.eq_of_mul_eq_mul_left hLpos hwithL
  have hKpos : 0 < K := Nat.zero_lt_of_lt (P.block (0 : V p n)).isLt
  have hKone : 1 ≤ K := hKpos
  have hTone : T ≤ Q := sameBlockCount_le P a
  have hKmul : p * (K / p) = K := Nat.mul_div_cancel' hdiv
  have hQdiv : p ∣ Q := by
    change p ∣ p ^ n
    exact dvd_pow_self p hn.ne'
  have hQmul : p * (Q / p) = Q := Nat.mul_div_cancel' hQdiv
  have hrpos : 0 < K / p := by
    by_contra hr
    simp only [not_lt, nonpos_iff_eq_zero] at hr
    rw [hr, mul_zero] at hKmul
    exact hKpos.ne' hKmul.symm
  have hrone : 1 ≤ K / p := hrpos
  have havgZ := congrArg (fun z : ℕ ↦ (z : ℤ)) havg
  have hKmulZ := congrArg (fun z : ℕ ↦ (z : ℤ)) hKmul
  have hQmulZ := congrArg (fun z : ℕ ↦ (z : ℤ)) hQmul
  norm_num only [Nat.cast_mul, Nat.cast_add] at havgZ hKmulZ hQmulZ
  rw [Nat.cast_sub hKone, Nat.cast_sub hrone, Nat.cast_sub hTone] at havgZ
  have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  rw [← hKmulZ, ← hQmulZ] at havgZ
  have hfactor :
      ((p : ℤ) - 1) * (((Q / p : ℕ) : ℤ) - ((K / p : ℕ) : ℤ) * T) = 0 := by
    calc
      ((p : ℤ) - 1) * (((Q / p : ℕ) : ℤ) - ((K / p : ℕ) : ℤ) * T) =
          ((p : ℤ) * (K / p : ℕ) - 1) * (Q / p : ℕ) -
            ((T : ℤ) * ((p : ℤ) * (K / p : ℕ) - 1) +
              ((p : ℤ) * (Q / p : ℕ) - T) * ((K / p : ℕ) - 1)) := by ring
      _ = 0 := sub_eq_zero.mpr havgZ
  have hpminus : (p : ℤ) - 1 ≠ 0 := by nlinarith
  have hsZ : ((Q / p : ℕ) : ℤ) = (K / p : ℕ) * T := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hpminus)
  have hresultZ : (K : ℤ) * T = Q := by
    calc
      (K : ℤ) * T = (p * (K / p : ℕ) : ℕ) * T := by rw [hKmul]
      _ = (p : ℤ) * ((K / p : ℕ) * T) := by push_cast; ring
      _ = (p : ℤ) * (Q / p : ℕ) := by rw [← hsZ]
      _ = Q := hQmulZ
  exact_mod_cast hresultZ

/-- Phase 1 endpoint: balanced nonzero derivatives for every induced function force the
partition depth to be a positive power of `p`, with exponent at most `n`. -/
theorem prime_power_depth_of_derivative_zero_count {p n K : ℕ} [NeZero p]
    (hp : p.Prime) (hn : 0 < n) (hdiv : p ∣ K)
    (P : BlockPartition p n K)
    (hzero : ∀ (ell : BalancedLabelingType p K) (a : V p n), a ≠ 0 →
      Fintype.card {x : V p n // derivative (induced P ell.1) a x = 0} = p ^ n / p) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ K = p ^ k := by
  letI : Fact p.Prime := ⟨hp⟩
  let a : V p n := fun _ ↦ 1
  have ha : a ≠ 0 := by
    intro h
    have hc := congrFun h ⟨0, hn⟩
    simpa [a] using hc
  have hKT : K * sameBlockCount P a = p ^ n :=
    double_counting_identity hp hn hdiv P a (fun ell ↦ hzero ell a ha)
  have hKdvd : K ∣ p ^ n := ⟨sameBlockCount P a, hKT.symm⟩
  obtain ⟨k, hkn, hK⟩ := (Nat.dvd_prime_pow hp).mp hKdvd
  have hkpos : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hpone : p ∣ 1 := by simpa [hk0, hK] using hdiv
    exact hp.ne_one (Nat.dvd_one.mp hpone)
  exact ⟨k, hkpos, hkn, hK⟩
end BentPartitionDepth
