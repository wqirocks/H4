import Sp4.Chains.Orientation

/-!
# Finite transportation core for weighted face pairing

On a regular oriented orbit, the signed coefficient list has total zero.
This file realizes the resulting transport plan by the explicit product
coupling.  Each coupling entry has two directed atoms, exchanged by `mate`.
-/

namespace Sp4
namespace OrbitChain

open scoped BigOperators

namespace RegularCoupling

noncomputable section

variable {K : Type*} [Fintype K] [DecidableEq K]
variable (c ori : K → ℝ)

def orientedValue (k : K) : ℝ := c k * ori k

abbrev Positive := {k : K // 0 < orientedValue c ori k}
abbrev Negative := {k : K // orientedValue c ori k < 0}

noncomputable instance positiveFintype : Fintype (Positive c ori) :=
  Fintype.ofFinite _

noncomputable instance negativeFintype : Fintype (Negative c ori) :=
  Fintype.ofFinite _

def positiveWeight (p : Positive c ori) : ℝ :=
  orientedValue c ori p.1

def negativeWeight (n : Negative c ori) : ℝ :=
  -orientedValue c ori n.1

abbrev Pair := Positive c ori × Negative c ori
abbrev Atom := Pair c ori × Bool

/-- `false` is the positive endpoint and `true` the negative endpoint. -/
def endpoint (a : Atom c ori) : K :=
  if a.2 then a.1.2.1 else a.1.1.1

def weight (r : Pair c ori) : ℝ :=
  productCoupling (positiveWeight c ori) (negativeWeight c ori) r.1 r.2

/-- Convert oriented coupling weights back to the original coefficient
orientation at each endpoint. -/
def atomCoeff (a : Atom c ori) : ℝ :=
  if a.2 then -ori a.1.2.1 * weight c ori a.1
  else ori a.1.1.1 * weight c ori a.1

/-- Swap the two directed atoms belonging to the same coupling entry. -/
def mate : Equiv.Perm (Atom c ori) where
  toFun a := (a.1, !a.2)
  invFun a := (a.1, !a.2)
  left_inv a := by
    rcases a with ⟨r, b⟩
    cases b <;> rfl
  right_inv a := by
    rcases a with ⟨r, b⟩
    cases b <;> rfl

@[simp]
theorem mate_apply (a : Atom c ori) : mate c ori a = (a.1, !a.2) := rfl

theorem mate_involutive (a : Atom c ori) :
    mate c ori (mate c ori a) = a := by
  cases a with
  | mk r b => cases b <;> rfl

theorem mate_ne (a : Atom c ori) : mate c ori a ≠ a := by
  cases a with
  | mk r b => cases b <;> simp [mate]

theorem positiveWeight_pos (p : Positive c ori) :
    0 < positiveWeight c ori p := p.2

theorem negativeWeight_pos (n : Negative c ori) :
    0 < negativeWeight c ori n := neg_pos.mpr n.2

theorem sum_positiveWeight_pos [Nonempty (Positive c ori)] :
    0 < ∑ p : Positive c ori, positiveWeight c ori p := by
  exact Finset.sum_pos (fun p _ ↦ positiveWeight_pos c ori p)
    Finset.univ_nonempty

theorem sum_positiveWeight_ne_zero [Nonempty (Positive c ori)] :
    (∑ p : Positive c ori, positiveWeight c ori p) ≠ 0 :=
  ne_of_gt (sum_positiveWeight_pos c ori)

theorem weight_pos [Nonempty (Positive c ori)] (r : Pair c ori) :
    0 < weight c ori r :=
  productCoupling_pos _ _ (positiveWeight_pos c ori)
    (negativeWeight_pos c ori) r.1 r.2

/-- Absolute coefficients of the two directed atoms are exactly the
positive coupling weight. -/
theorem abs_atomCoeff
    [Nonempty (Positive c ori)]
    (hori : ∀ k, ori k = 1 ∨ ori k = -1)
    (a : Atom c ori) :
    |atomCoeff c ori a| = weight c ori a.1 := by
  rcases a with ⟨⟨p, n⟩, b⟩
  cases b <;>
    simp only [atomCoeff, Bool.false_eq_true, if_false, if_true,
      abs_mul, abs_neg]
  · rcases hori p.1 with h | h <;>
      rw [h] <;> simp [abs_of_pos (weight_pos c ori (p, n))]
  · rcases hori n.1 with h | h <;>
      rw [h] <;> simp [abs_of_pos (weight_pos c ori (p, n))]

/-- The orientation covariance of two endpoints is exactly the sign rule
required by an oriented atom pairing. -/
theorem coeff_transport_of_orientation
    (a : Atom c ori) (σ : Equiv.Perm (Fin 4))
    (htransport : ori (endpoint c ori (mate c ori a)) =
      permSign ℝ σ * ori (endpoint c ori a)) :
    atomCoeff c ori (mate c ori a) * permSign ℝ σ =
      -atomCoeff c ori a := by
  rcases a with ⟨⟨p, n⟩, b⟩
  cases b
  · change ori n.1 = permSign ℝ σ * ori p.1 at htransport
    change (-ori n.1 * weight c ori (p, n)) * permSign ℝ σ =
      -(ori p.1 * weight c ori (p, n))
    rw [htransport]
    calc
      (-(permSign ℝ σ * ori p.1) * weight c ori (p, n)) *
          permSign ℝ σ =
        -(ori p.1 * weight c ori (p, n)) *
          (permSign ℝ σ * permSign ℝ σ) := by ring
      _ = -(ori p.1 * weight c ori (p, n)) := by
        rw [permSign_sq, mul_one]
  · change ori p.1 = permSign ℝ σ * ori n.1 at htransport
    change (ori p.1 * weight c ori (p, n)) * permSign ℝ σ =
      -(-ori n.1 * weight c ori (p, n))
    rw [htransport]
    calc
      ((permSign ℝ σ * ori n.1) * weight c ori (p, n)) *
          permSign ℝ σ =
        (ori n.1 * weight c ori (p, n)) *
          (permSign ℝ σ * permSign ℝ σ) := by ring
      _ = -(-ori n.1 * weight c ori (p, n)) := by
        rw [permSign_sq, mul_one]
        ring

/-- Row refinement for a positive occurrence. -/
theorem coeff_refinement_pos
    (heq : (∑ p : Positive c ori, positiveWeight c ori p) =
      ∑ n : Negative c ori, negativeWeight c ori n)
    (hne : (∑ p : Positive c ori, positiveWeight c ori p) ≠ 0)
    (hori : ∀ k, ori k = 1 ∨ ori k = -1)
    (k : K) (hk : 0 < orientedValue c ori k) :
    (∑ a ∈ Finset.univ.filter
      (fun a : Atom c ori => endpoint c ori a = k), atomCoeff c ori a) =
      c k := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, endpoint, atomCoeff, Bool.false_eq_true,
    if_false, Bool.if_true_right, Bool.true_eq_false, if_true, add_zero]
  rw [Finset.sum_add_distrib]
  have hN (n : Negative c ori) : n.1 ≠ k := by
    intro h
    have hn := n.2
    change orientedValue c ori n.1 < 0 at hn
    rw [h] at hn
    linarith
  have hfirst :
      (∑ x : Pair c ori,
        if x.2.1 = k then
          -ori x.2.1 * weight c ori x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg (hN x.2)]
  rw [hfirst, zero_add, Fintype.sum_prod_type]
  let pk : Positive c ori := ⟨k, hk⟩
  calc
    (∑ p : Positive c ori, ∑ n : Negative c ori,
        if p.1 = k then ori p.1 * weight c ori (p, n) else 0) =
      ∑ n : Negative c ori,
        if pk.1 = k then ori pk.1 * weight c ori (pk, n) else 0 := by
        apply Finset.sum_eq_single pk
        · intro p _ hp
          have hpk : p.1 ≠ k := by
            intro h
            exact hp (Subtype.ext h)
          simp [hpk]
        · simp
    _ = ∑ n : Negative c ori,
        ori pk.1 * weight c ori (pk, n) := by simp [pk]
    _ = ori k * ∑ n : Negative c ori, weight c ori (pk, n) := by
      rw [Finset.mul_sum]
    _ = ori k * positiveWeight c ori pk := by
      change ori k *
        (∑ n : Negative c ori,
          productCoupling (positiveWeight c ori)
            (negativeWeight c ori) pk n) = _
      rw [sum_productCoupling_row _ _ heq hne pk]
  dsimp [positiveWeight, orientedValue, pk]
  rcases hori k with h | h <;> rw [h] <;> ring

/-- Column refinement for a negative occurrence. -/
theorem coeff_refinement_neg
    (hne : (∑ p : Positive c ori, positiveWeight c ori p) ≠ 0)
    (hori : ∀ k, ori k = 1 ∨ ori k = -1)
    (k : K) (hk : orientedValue c ori k < 0) :
    (∑ a ∈ Finset.univ.filter
      (fun a : Atom c ori => endpoint c ori a = k), atomCoeff c ori a) =
      c k := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, endpoint, atomCoeff, Bool.false_eq_true,
    if_false, Bool.true_eq_false, if_true]
  rw [Finset.sum_add_distrib]
  have hP (p : Positive c ori) : p.1 ≠ k := by
    intro h
    have hp := p.2
    change 0 < orientedValue c ori p.1 at hp
    rw [h] at hp
    linarith
  have hsecond :
      (∑ x : Pair c ori,
        if x.1.1 = k then ori x.1.1 * weight c ori x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg (hP x.1)]
  rw [hsecond, add_zero, Fintype.sum_prod_type]
  let nk : Negative c ori := ⟨k, hk⟩
  rw [Finset.sum_comm]
  calc
    (∑ n : Negative c ori, ∑ p : Positive c ori,
        if n.1 = k then -ori n.1 * weight c ori (p, n) else 0) =
      ∑ p : Positive c ori,
        if nk.1 = k then -ori nk.1 * weight c ori (p, nk) else 0 := by
        apply Finset.sum_eq_single nk
        · intro n _ hn
          have hnk : n.1 ≠ k := by
            intro h
            exact hn (Subtype.ext h)
          simp [hnk]
        · simp
    _ = ∑ p : Positive c ori,
        -ori nk.1 * weight c ori (p, nk) := by simp [nk]
    _ = -ori k * ∑ p : Positive c ori, weight c ori (p, nk) := by
      rw [Finset.mul_sum]
    _ = -ori k * negativeWeight c ori nk := by
      change -ori k *
        (∑ p : Positive c ori,
          productCoupling (positiveWeight c ori)
            (negativeWeight c ori) p nk) = _
      rw [sum_productCoupling_col _ _ hne nk]
  dsimp [negativeWeight, orientedValue, nk]
  rcases hori k with h | h <;> rw [h] <;> ring

/-- Row refinement preserves absolute mass at a positive occurrence. -/
theorem mass_refinement_pos
    (heq : (∑ p : Positive c ori, positiveWeight c ori p) =
      ∑ n : Negative c ori, negativeWeight c ori n)
    (hne : (∑ p : Positive c ori, positiveWeight c ori p) ≠ 0)
    (hori : ∀ k, ori k = 1 ∨ ori k = -1)
    (k : K) (hk : 0 < orientedValue c ori k) :
    (∑ a ∈ Finset.univ.filter
      (fun a : Atom c ori => endpoint c ori a = k),
      |atomCoeff c ori a|) = |c k| := by
  classical
  let pk : Positive c ori := ⟨k, hk⟩
  letI : Nonempty (Positive c ori) := ⟨pk⟩
  simp_rw [abs_atomCoeff c ori hori]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, endpoint, Bool.false_eq_true, if_false,
    Bool.true_eq_false, if_true]
  rw [Finset.sum_add_distrib]
  have hN (n : Negative c ori) : n.1 ≠ k := by
    intro h
    have hn := n.2
    change orientedValue c ori n.1 < 0 at hn
    rw [h] at hn
    linarith
  have hfirst :
      (∑ x : Pair c ori,
        if x.2.1 = k then weight c ori x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg (hN x.2)]
  rw [hfirst, zero_add, Fintype.sum_prod_type]
  calc
    (∑ p : Positive c ori, ∑ n : Negative c ori,
        if p.1 = k then weight c ori (p, n) else 0) =
      ∑ n : Negative c ori,
        if pk.1 = k then weight c ori (pk, n) else 0 := by
        apply Finset.sum_eq_single pk
        · intro p _ hp
          have hpk : p.1 ≠ k := by
            intro h
            exact hp (Subtype.ext h)
          simp [hpk]
        · simp
    _ = ∑ n : Negative c ori, weight c ori (pk, n) := by simp [pk]
    _ = positiveWeight c ori pk := by
      change (∑ n : Negative c ori,
          productCoupling (positiveWeight c ori)
            (negativeWeight c ori) pk n) = _
      rw [sum_productCoupling_row _ _ heq hne pk]
    _ = |c k| := by
      dsimp [positiveWeight, orientedValue, pk]
      change 0 < c k * ori k at hk
      rcases hori k with h | h
      · rw [h] at hk ⊢
        simp only [mul_one] at hk ⊢
        exact (abs_of_pos hk).symm
      · rw [h] at hk ⊢
        simp only [mul_neg, mul_one] at hk ⊢
        rw [abs_of_neg (by linarith)]

/-- Column refinement preserves absolute mass at a negative occurrence. -/
theorem mass_refinement_neg
    (hne : (∑ p : Positive c ori, positiveWeight c ori p) ≠ 0)
    (hori : ∀ k, ori k = 1 ∨ ori k = -1)
    (k : K) (hk : orientedValue c ori k < 0) :
    (∑ a ∈ Finset.univ.filter
      (fun a : Atom c ori => endpoint c ori a = k),
      |atomCoeff c ori a|) = |c k| := by
  classical
  have hpos : Nonempty (Positive c ori) := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    letI : IsEmpty (Positive c ori) := hempty
    simpa using hne
  letI : Nonempty (Positive c ori) := hpos
  simp_rw [abs_atomCoeff c ori hori]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, endpoint, Bool.false_eq_true, if_false,
    Bool.true_eq_false, if_true]
  rw [Finset.sum_add_distrib]
  have hP (q : Positive c ori) : q.1 ≠ k := by
    intro h
    have hq := q.2
    change 0 < orientedValue c ori q.1 at hq
    rw [h] at hq
    linarith
  have hsecond :
      (∑ x : Pair c ori,
        if x.1.1 = k then weight c ori x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg (hP x.1)]
  rw [hsecond, add_zero, Fintype.sum_prod_type]
  let nk : Negative c ori := ⟨k, hk⟩
  rw [Finset.sum_comm]
  calc
    (∑ n : Negative c ori, ∑ q : Positive c ori,
        if n.1 = k then weight c ori (q, n) else 0) =
      ∑ q : Positive c ori,
        if nk.1 = k then weight c ori (q, nk) else 0 := by
        apply Finset.sum_eq_single nk
        · intro n _ hn
          have hnk : n.1 ≠ k := by
            intro h
            exact hn (Subtype.ext h)
          simp [hnk]
        · simp
    _ = ∑ q : Positive c ori, weight c ori (q, nk) := by simp [nk]
    _ = negativeWeight c ori nk := by
      change (∑ q : Positive c ori,
          productCoupling (positiveWeight c ori)
            (negativeWeight c ori) q nk) = _
      rw [sum_productCoupling_col _ _ hne nk]
    _ = |c k| := by
      dsimp [negativeWeight, orientedValue, nk]
      change c k * ori k < 0 at hk
      rcases hori k with h | h
      · rw [h] at hk ⊢
        simp only [mul_one] at hk ⊢
        rw [abs_of_neg hk]
      · rw [h] at hk ⊢
        simp only [mul_neg, mul_one, neg_neg] at hk ⊢
        exact (abs_of_pos (neg_lt_zero.mp hk)).symm

end

end RegularCoupling

/-! ## The two-copy splitting on an orientation-singular orbit -/

namespace SingularSplitting

noncomputable section

variable {K : Type*} [Fintype K] [DecidableEq K]
variable (c : K → ℝ)

abbrev Atom (_c : K → ℝ) := K × Bool

def endpoint (a : Atom c) : K := a.1

/-- Each occurrence is split into two equal directed atoms. -/
def atomCoeff (a : Atom c) : ℝ := c a.1 / 2

def mate : Equiv.Perm (Atom c) where
  toFun a := (a.1, !a.2)
  invFun a := (a.1, !a.2)
  left_inv a := by
    rcases a with ⟨k, b⟩
    cases b <;> rfl
  right_inv a := by
    rcases a with ⟨k, b⟩
    cases b <;> rfl

@[simp]
theorem mate_apply (a : Atom c) : mate c a = (a.1, !a.2) := rfl

theorem mate_involutive (a : Atom c) : mate c (mate c a) = a := by
  rcases a with ⟨k, b⟩
  cases b <;> rfl

theorem mate_ne (a : Atom c) : mate c a ≠ a := by
  rcases a with ⟨k, b⟩
  cases b <;> simp [mate]

/-- The two half-atoms recover the original coefficient. -/
theorem coeff_refinement (k : K) :
    (∑ a ∈ Finset.univ.filter
      (fun a : Atom c ↦ endpoint c a = k), atomCoeff c a) = c k := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, endpoint, atomCoeff]
  calc
    (∑ x : K, ((if x = k then c x / 2 else 0) +
        (if x = k then c x / 2 else 0))) =
      (c k / 2 + c k / 2) := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']
    _ = c k := by ring

/-- The two half-atoms also recover the original absolute mass. -/
theorem mass_refinement (k : K) :
    (∑ a ∈ Finset.univ.filter
      (fun a : Atom c ↦ endpoint c a = k), |atomCoeff c a|) = |c k| := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, endpoint, atomCoeff]
  calc
    (∑ x : K, ((if x = k then |c x / 2| else 0) +
        (if x = k then |c x / 2| else 0))) =
      (|c k / 2| + |c k / 2|) := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']
    _ = |c k| := by
      rw [abs_div]
      norm_num

/-- An odd self-transport supplies precisely the negative sign between the
two equal half-atoms. -/
theorem coeff_transport_of_odd
    (a : Atom c) (σ : Equiv.Perm (Fin 4))
    (hodd : permSign ℝ σ = -1) :
    atomCoeff c (mate c a) * permSign ℝ σ =
      -atomCoeff c a := by
  rw [hodd]
  simp [atomCoeff, mate]

end

end SingularSplitting

end OrbitChain
end Sp4
