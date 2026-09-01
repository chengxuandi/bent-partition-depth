import BentPartitionDepth.CyclotomicMultiplicity
import Mathlib.Analysis.RCLike.Basic

/-!
# Walsh flatness and balanced derivatives

This file proves the finite Wiener--Khinchin identity for the concrete Walsh transform
and derives balanced nonzero derivatives over the prime field.
-/

namespace BentPartitionDepth

open scoped BigOperators ComplexConjugate
open Finset

lemma dot_add {p n : ℕ} (b x y : V p n) : dot b (x + y) = dot b x + dot b y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma add_dot {p n : ℕ} (b c x : V p n) : dot (b + c) x = dot b x + dot c x := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_sub {p n : ℕ} (b x y : V p n) : dot b (x - y) = dot b x - dot b y := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

/-- For a prime modulus, the canonical additive character takes the value one only at zero. -/
lemma baseChar_eq_one_iff {p : ℕ} [NeZero p] (hp : p.Prime) (c : ZMod p) :
    baseChar p c = 1 ↔ c = 0 := by
  have hprim : AddChar.IsPrimitive (baseChar p) := by
    exact AddChar.zmodChar_primitive_of_primitive_root p (omega_isPrimitiveRoot hp.ne_zero)
  exact hprim.zmod_char_eq_one_iff p c

/-- The additive character `b ↦ omega^(dot b a)`. -/
noncomputable def dotAddChar {p n : ℕ} [NeZero p] (a : V p n) : AddChar (V p n) ℂ :=
  (baseChar p).compAddMonoidHom
    { toFun := fun b ↦ dot b a
      map_zero' := by simp [dot]
      map_add' := by intro b c; exact add_dot b c a }

@[simp] lemma dotAddChar_apply {p n : ℕ} [NeZero p] (a b : V p n) :
    dotAddChar a b = baseChar p (dot b a) := rfl

lemma dotAddChar_ne_one {p n : ℕ} [NeZero p] (hp : p.Prime)
    {a : V p n} (ha : a ≠ 0) : dotAddChar a ≠ 1 := by
  have hcoord : ∃ i : Fin n, a i ≠ 0 := by
    by_contra h
    push_neg at h
    apply ha
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  intro hchar
  have heval := DFunLike.congr_fun hchar (Pi.single i (1 : ZMod p))
  have hone : baseChar p (a i) = 1 := by
    simpa [dotAddChar, dot, Pi.single_apply] using heval
  exact hi ((baseChar_eq_one_iff hp (a i)).mp hone)

/-- Orthogonality of the dot-product characters. -/
lemma sum_baseChar_dot {p n : ℕ} [NeZero p] (hp : p.Prime) (a : V p n) :
    ∑ b : V p n, baseChar p (dot b a) = if a = 0 then (p ^ n : ℂ) else 0 := by
  by_cases ha : a = 0
  · subst a
    simp [dot, V]
  · rw [if_neg ha]
    exact AddChar.sum_eq_zero_of_ne_one (dotAddChar_ne_one hp ha)

/-- Additive autocorrelation in direction `a`. -/
noncomputable def autocorrelation {p n : ℕ} [NeZero p]
    (f : V p n → ZMod p) (a : V p n) : ℂ :=
  ∑ x : V p n, baseChar p (derivative f a x)

/-- Finite Wiener--Khinchin identity for the chosen Walsh-sign convention. -/
theorem wiener_khinchin {p n : ℕ} [NeZero p]
    (f : V p n → ZMod p) (b : V p n) :
    (Complex.normSq (walsh f b) : ℂ) =
      ∑ a : V p n, autocorrelation f a * baseChar p (-dot b a) := by
  rw [Complex.normSq_eq_conj_mul_self]
  calc
    conj (walsh f b) * walsh f b =
        (∑ y : V p n, conj (baseChar p (f y - dot b y))) *
          ∑ x : V p n, baseChar p (f x - dot b x) := by
      simp only [walsh, map_sum]
    _ = ∑ y : V p n, ∑ x : V p n,
          conj (baseChar p (f y - dot b y)) * baseChar p (f x - dot b x) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
    _ = ∑ y : V p n, ∑ a : V p n,
          conj (baseChar p (f y - dot b y)) *
            baseChar p (f (y + a) - dot b (y + a)) := by
      apply Finset.sum_congr rfl
      intro y _
      exact (Fintype.sum_equiv (Equiv.addLeft y)
        (fun a : V p n ↦ conj (baseChar p (f y - dot b y)) *
          baseChar p (f (y + a) - dot b (y + a)))
        (fun x : V p n ↦ conj (baseChar p (f y - dot b y)) *
          baseChar p (f x - dot b x)) (fun _ ↦ rfl)).symm
    _ = ∑ y : V p n, ∑ a : V p n,
          baseChar p (derivative f a y) * baseChar p (-dot b a) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [derivative, dot_add]
      abel
    _ = ∑ a : V p n, ∑ y : V p n,
          baseChar p (derivative f a y) * baseChar p (-dot b a) := by
      rw [Finset.sum_comm]
    _ = ∑ a : V p n, autocorrelation f a * baseChar p (-dot b a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [autocorrelation, Finset.sum_mul]

/-- Walsh flatness forces every nonzero additive autocorrelation to vanish. -/
theorem autocorrelation_eq_zero_of_isBent {p n : ℕ} [NeZero p]
    (hp : p.Prime) {f : V p n → ZMod p} (hf : IsBent f)
    {a : V p n} (ha : a ≠ 0) : autocorrelation f a = 0 := by
  let Q := p ^ n
  have hflat (b : V p n) :
      ∑ d : V p n, autocorrelation f d * baseChar p (-dot b d) = (Q : ℂ) := by
    rw [← wiener_khinchin]
    exact_mod_cast hf b
  have hflatSum :
      ∑ b : V p n, (Q : ℂ) * baseChar p (dot b a) = 0 := by
    rw [← Finset.mul_sum, sum_baseChar_dot hp, if_neg ha, mul_zero]
  have hzero :
      ∑ b : V p n,
        (∑ d : V p n, autocorrelation f d * baseChar p (-dot b d)) *
          baseChar p (dot b a) = 0 := by
    calc
      (∑ b : V p n,
        (∑ d : V p n, autocorrelation f d * baseChar p (-dot b d)) *
          baseChar p (dot b a)) =
          ∑ b : V p n, (Q : ℂ) * baseChar p (dot b a) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hflat b]
      _ = 0 := hflatSum
  have htransform :
      ∑ b : V p n,
        (∑ d : V p n, autocorrelation f d * baseChar p (-dot b d)) *
          baseChar p (dot b a) =
      ∑ d : V p n, autocorrelation f d *
        (∑ b : V p n, baseChar p (dot b (a - d))) := by
    calc
      (∑ b : V p n,
        (∑ d : V p n, autocorrelation f d * baseChar p (-dot b d)) *
          baseChar p (dot b a)) =
          ∑ b : V p n, ∑ d : V p n,
            (autocorrelation f d * baseChar p (-dot b d)) *
              baseChar p (dot b a) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_mul]
      _ = ∑ d : V p n, ∑ b : V p n,
          (autocorrelation f d * baseChar p (-dot b d)) *
            baseChar p (dot b a) := by rw [Finset.sum_comm]
      _ = ∑ d : V p n, autocorrelation f d *
          (∑ b : V p n, baseChar p (dot b (a - d))) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [mul_assoc, ← AddChar.map_add_eq_mul]
        congr 2
        rw [dot_sub]
        abel
  have hCaQ : autocorrelation f a * (Q : ℂ) = 0 := by
    rw [htransform] at hzero
    simp_rw [sum_baseChar_dot hp] at hzero
    simpa only [sub_eq_zero, mul_ite, mul_zero, Fintype.sum_ite_eq, Q, Nat.cast_pow] using hzero
  have hQne : (Q : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero n hp.ne_zero)
  exact (mul_eq_zero.mp hCaQ).resolve_right hQne

/-- Multiplicity of one derivative value, indexed by the canonical `Fin p` model of `ZMod p`. -/
def derivativeMultiplicity {p n : ℕ} [NeZero p]
    (f : V p n → ZMod p) (a : V p n) (c : Fin p) : ℕ :=
  Fintype.card {x : V p n // derivative f a x = ZMod.finEquiv p c}

/-- Regrouping the autocorrelation sum by derivative values. -/
lemma autocorrelation_eq_multiplicity_sum {p n : ℕ} [NeZero p]
    (f : V p n → ZMod p) (a : V p n) :
    autocorrelation f a =
      ∑ c : Fin p, (derivativeMultiplicity f a c : ℂ) * omega p ^ c.val := by
  rw [autocorrelation]
  calc
    (∑ x : V p n, baseChar p (derivative f a x)) =
        ∑ c : ZMod p,
          ∑ x : {x : V p n // derivative f a x = c},
            baseChar p (derivative f a x.1) := by
      exact (Fintype.sum_fiberwise (fun x : V p n ↦ derivative f a x)
        (fun x ↦ baseChar p (derivative f a x))).symm
    _ = ∑ c : ZMod p,
          (Fintype.card {x : V p n // derivative f a x = c} : ℂ) * baseChar p c := by
      apply Finset.sum_congr rfl
      intro c _
      simp only [show ∀ x : {x : V p n // derivative f a x = c},
          baseChar p (derivative f a x.1) = baseChar p c from fun x ↦ congrArg _ x.2,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ c : Fin p, (derivativeMultiplicity f a c : ℂ) * omega p ^ c.val := by
      rw [← (ZMod.finEquiv p).sum_comp]
      apply Finset.sum_congr rfl
      intro c _
      change (Fintype.card {x : V p n // derivative f a x = ZMod.finEquiv p c} : ℂ) *
          baseChar p (ZMod.finEquiv p c) =
        (Fintype.card {x : V p n // derivative f a x = ZMod.finEquiv p c} : ℂ) *
          omega p ^ c.val
      rw [baseChar_apply]
      congr 2
      cases p with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ p => rfl

lemma derivativeMultiplicity_sum {p n : ℕ} [NeZero p]
    (f : V p n → ZMod p) (a : V p n) :
    ∑ c : Fin p, derivativeMultiplicity f a c = p ^ n := by
  let E : (Σ c : Fin p,
      {x : V p n // derivative f a x = ZMod.finEquiv p c}) ≃ V p n :=
    { toFun := fun q ↦ q.2.1
      invFun := fun x ↦ ⟨(ZMod.finEquiv p).symm (derivative f a x), x, by simp⟩
      left_inv := by
        rintro ⟨c, x, hx⟩
        have hc : (ZMod.finEquiv p).symm (derivative f a x) = c := by
          simpa using congrArg (ZMod.finEquiv p).symm hx
        subst c
        rfl
      right_inv := by intro x; rfl }
  calc
    (∑ c : Fin p, derivativeMultiplicity f a c) =
        Nat.card (Σ c : Fin p,
          {x : V p n // derivative f a x = ZMod.finEquiv p c}) := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro c _
      rw [derivativeMultiplicity, Nat.card_eq_fintype_card]
    _ = Nat.card (V p n) := Nat.card_congr E
    _ = p ^ n := by simp [V]

/-- A `p`-ary bent function has a balanced derivative in every nonzero direction. -/
theorem derivative_balanced_of_isBent {p n : ℕ} [NeZero p]
    (hp : p.Prime) (hn : 0 < n) {f : V p n → ZMod p}
    (hf : IsBent f) {a : V p n} (ha : a ≠ 0) : IsBalanced (derivative f a) := by
  have hcorr : autocorrelation f a = 0 := autocorrelation_eq_zero_of_isBent hp hf ha
  have hroot :
      ∑ c : Fin p, (derivativeMultiplicity f a c : ℂ) * omega p ^ c.val = 0 := by
    rw [← autocorrelation_eq_multiplicity_sum]
    exact hcorr
  have hpow := prime_root_sum_multiplicity_eq_pow hp hn
    (derivativeMultiplicity f a) hroot (derivativeMultiplicity_sum f a)
  intro c
  calc
    Fintype.card {x : V p n // derivative f a x = c} = p ^ (n - 1) := by
      simpa [derivativeMultiplicity] using hpow ((ZMod.finEquiv p).symm c)
    _ = Fintype.card (V p n) / p := by
      cases n with
      | zero => omega
      | succ k => simp [V, pow_succ, hp.ne_zero, Nat.mul_comm]

/-- The zero-value specialization used by the double-counting theorem. -/
theorem derivative_zero_count_of_isBent {p n : ℕ} [NeZero p]
    (hp : p.Prime) (hn : 0 < n) {f : V p n → ZMod p}
    (hf : IsBent f) {a : V p n} (ha : a ≠ 0) :
    Fintype.card {x : V p n // derivative f a x = 0} = p ^ n / p := by
  simpa [IsBalanced, V] using (derivative_balanced_of_isBent hp hn hf ha 0)

end BentPartitionDepth
