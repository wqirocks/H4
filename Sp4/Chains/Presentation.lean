import Sp4.Chains.FacePairing

/-!
# Canonical support presentations of finite raw chains

A `Finsupp` chain already contains a canonical finite weighted presentation:
its nonzero support.  This module packages that presentation without changing
either the represented quotient chain or its displayed `ℓ1` mass.
-/

namespace Sp4
namespace OrbitChain

open scoped BigOperators

noncomputable section

/-- The canonical finite index type of nonzero generators in a raw chain. -/
abbrev SupportIndex {n : ℕ} (c : Raw ℝ n) := {x // x ∈ c.support}

/-- Reconstruction of a raw chain from its canonical support presentation. -/
theorem raw_eq_sum_support {n : ℕ} (c : Raw ℝ n) :
    (∑ s : SupportIndex c, c s.1 • generator s.1) = c := by
  classical
  rw [Finset.univ_eq_attach c.support]
  calc
    (∑ s ∈ c.support.attach, c s.1 • generator s.1) =
        ∑ x ∈ c.support, c x • generator x :=
      Finset.sum_attach c.support (fun x ↦ c x • generator x)
    _ = c.sum (fun x a ↦ a • generator x) := rfl
    _ = c := by simpa [generator] using c.sum_single

/-- The displayed coefficient mass of the support presentation is exactly
the raw `ℓ1` mass, not merely bounded by it. -/
theorem sum_abs_support_eq_rawMass {n : ℕ} (c : Raw ℝ n) :
    (∑ s : SupportIndex c, |c s.1|) = rawMass c := by
  classical
  rw [Finset.univ_eq_attach c.support]
  exact Finset.sum_attach c.support (fun x ↦ |c x|)

/-- A raw five-chain whose quotient class is a cycle becomes a finite
weighted facet presentation on its nonzero support. -/
def supportPresentation (c : Raw ℝ 5)
    (hcycle : boundary ℝ 4 ((relations ℝ 5).mkQ c) = 0) :
    WeightedFacetPresentation (SupportIndex c) where
  facet := fun s ↦ s.1
  coeff := fun s ↦ c s.1
  coeff_ne := fun s ↦ Finsupp.mem_support_iff.mp s.2
  isCycle := by
    have hmk :
        (∑ s : SupportIndex c, c s.1 • ofConfig (R := ℝ) s.1) =
          (relations ℝ 5).mkQ c := by
      have h := congrArg (relations ℝ 5).mkQ (raw_eq_sum_support c)
      simpa [ofConfig] using h
    rw [hmk]
    exact hcycle

/-- The support presentation associated to any chosen raw presentation of a
quotient cycle. -/
def supportPresentationOfCycle
    (z : Module ℝ 5) (hz : boundary ℝ 4 z = 0)
    (c : Raw ℝ 5) (hc : (relations ℝ 5).mkQ c = z) :
    WeightedFacetPresentation (SupportIndex c) :=
  supportPresentation c (by rw [hc]; exact hz)

@[simp]
theorem supportPresentation_facet
    (c : Raw ℝ 5)
    (hcycle : boundary ℝ 4 ((relations ℝ 5).mkQ c) = 0)
    (s : SupportIndex c) :
    (supportPresentation c hcycle).facet s = s.1 := rfl

@[simp]
theorem supportPresentation_coeff
    (c : Raw ℝ 5)
    (hcycle : boundary ℝ 4 ((relations ℝ 5).mkQ c) = 0)
    (s : SupportIndex c) :
    (supportPresentation c hcycle).coeff s = c s.1 := rfl

theorem supportPresentation_displayedMass
    (c : Raw ℝ 5)
    (hcycle : boundary ℝ 4 ((relations ℝ 5).mkQ c) = 0) :
    (∑ s : SupportIndex c, |(supportPresentation c hcycle).coeff s|) =
      rawMass c :=
  sum_abs_support_eq_rawMass c

end
end OrbitChain
end Sp4
