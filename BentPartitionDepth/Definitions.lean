import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Bent partitions: basic definitions

This file fixes the concrete model `V = (ZMod p)^n`, the standard dot product,
the canonical complex additive character of `ZMod p`, Walsh coefficients,
balanced labelings, and block assignments.
-/

namespace BentPartitionDepth

open scoped BigOperators ComplexConjugate
open Finset

/-- The vector space `F_p^n`, represented as coordinate functions. -/
abbrev V (p n : ℕ) := Fin n → ZMod p

/-- The standard `ZMod p`-valued dot product. -/
def dot {p n : ℕ} (b x : V p n) : ZMod p :=
  ∑ i, b i * x i

/-- The canonical primitive `p`-th root of unity. -/
noncomputable def omega (p : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / p)

lemma omega_isPrimitiveRoot {p : ℕ} (hp0 : p ≠ 0) :
    IsPrimitiveRoot (omega p) p := by
  simpa [omega] using Complex.isPrimitiveRoot_exp p hp0

/-- The canonical additive character `c ↦ omega(p)^c` on `ZMod p`. -/
noncomputable def baseChar (p : ℕ) [NeZero p] : AddChar (ZMod p) ℂ :=
  AddChar.zmodChar p (omega_isPrimitiveRoot (p := p) (NeZero.ne p)).pow_eq_one

@[simp] lemma baseChar_apply (p : ℕ) [NeZero p] (c : ZMod p) :
    baseChar p c = omega p ^ c.val :=
  rfl

/-- The derivative of a `p`-ary function in direction `a`. -/
def derivative {p n : ℕ} (f : V p n → ZMod p) (a x : V p n) : ZMod p :=
  f (x + a) - f x

/-- Every output value occurs equally often. -/
def IsBalanced {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℕ} [NeZero p] (g : α → ZMod p) : Prop :=
  ∀ c : ZMod p, Fintype.card {x : α // g x = c} = Fintype.card α / p

/-- A balanced labeling assigns exactly `K / p` block indices to every field value. -/
def IsBalancedLabeling {p K : ℕ} [NeZero p] (ell : Fin K → ZMod p) : Prop :=
  ∀ c : ZMod p, Fintype.card {i : Fin K // ell i = c} = K / p

/-- A partition is represented by its unique block-index map; surjectivity means all blocks
are nonempty. -/
structure BlockPartition (p n K : ℕ) [NeZero p] where
  block : V p n → Fin K
  surjective : Function.Surjective block

/-- The function induced by a labeling of the blocks. -/
def induced {p n K : ℕ} [NeZero p] (P : BlockPartition p n K)
    (ell : Fin K → ZMod p) : V p n → ZMod p :=
  fun x ↦ ell (P.block x)

/-- The Walsh coefficient with the paper's sign convention. -/
noncomputable def walsh {p n : ℕ} [NeZero p] (f : V p n → ZMod p)
    (b : V p n) : ℂ :=
  ∑ x : V p n, baseChar p (f x - dot b x)

/-- Walsh-flat bentness, written in the exactly equivalent squared-norm form. -/
def IsBent {p n : ℕ} [NeZero p] (f : V p n → ZMod p) : Prop :=
  ∀ b : V p n, Complex.normSq (walsh f b) = (p ^ n : ℝ)

/-- The paper's universal quantifier over all balanced block labelings. -/
def IsBentPartition {p n K : ℕ} [NeZero p] (P : BlockPartition p n K) : Prop :=
  ∀ ell : Fin K → ZMod p, IsBalancedLabeling ell → IsBent (induced P ell)

/-- Ordered count of points whose translate stays in the same block. -/
def sameBlockCount {p n K : ℕ} [NeZero p] (P : BlockPartition p n K)
    (a : V p n) : ℕ :=
  Fintype.card {x : V p n // P.block x = P.block (x + a)}

end BentPartitionDepth
