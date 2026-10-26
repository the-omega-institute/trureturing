/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Six actual descendant three-field words share an infinite vector series. -/

import D5.S3.VertexAlgebra.FormalSeries.UngradedLocalWordSeries
import D5.S3.VertexAlgebra.Sectors.LatticeSectorBorcherds

/-!
The fields and intertwiners below are the original canonical lattice fields.
The imported suppliers retain their Bakalov--Kac, Matsuo--Nagatomo and Carnahan
attributions. This is finite-word common support, not a sewing/coherence law.
proof_shape: actual_three_field_common_series: bind-only
This common-series helper is consumed by the actual inner iterate transport.
Its mathematical suppliers are stateField_locality, common_cleared_fields,
inclusion_canonical and charge_homogeneity. Projection and finite convolution
transport the supplied common array to the total-charge sector. The signed
inner collision inference belongs to the consuming transport theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorThreeFieldCommonSeries

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner UniformGradedLocalCorrelator UngradedLocalWordSeries
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

/-- Three labelled actual fields, including arbitrary oscillator descendants.
Only the labels are distinct; charges and fields may repeat. -/
def labelledFields (D : LatticeData) (c : Fin 3 → Charge D)
    (s : Fin 3 → Oscillator D) : Fin 3 → VertexOperator ℂ (Carrier D) :=
  fun i => Y D (inclusion D (c i) (s i))

/-- The literal three nested canonical intertwiners, with exponents attached
to their original field labels, for an arbitrary fourth sector input. -/
def nestedCanonical (D : LatticeData) (c : Fin 3 → Charge D)
    (s : Fin 3 → Oscillator D) (δ : Charge D) (w : Sector D δ)
    (i j l : Fin 3) (e : Exponent 3) : Oscillator D :=
  canonical D (c i) (c j + (c l + δ)) (s i) (-e i - 1)
    (canonical D (c j) (c l + δ) (s j) (-e j - 1)
      (canonical D (c l) δ (s l) (-e l - 1) w))

private theorem word_three (D : LatticeData) (c : Fin 3 → Charge D)
    (s : Fin 3 → Oscillator D) (δ : Charge D) (w : Sector D δ)
    (i j l : Fin 3) (e : Exponent 3) :
    coefficientDistribution (labelledFields D c s) (inclusion D δ w) 1 [i, j, l] e =
      inclusion D (c i + (c j + (c l + δ)))
        (nestedCanonical D c s δ w i j l e) := by
  change ((Y D (inclusion D (c i) (s i)))[[-e i - 1]])
    (((Y D (inclusion D (c j) (s j)))[[-e j - 1]])
      (((Y D (inclusion D (c l) (s l)))[[-e l - 1]]) (inclusion D δ w))) = _
  rw [← inclusion_canonical D (c l) δ (s l) w (-e l - 1),
    ← inclusion_canonical D (c j) (c l + δ) (s j)
      (canonical D (c l) δ (s l) (-e l - 1) w) (-e j - 1),
    ← inclusion_canonical D (c i) (c j + (c l + δ)) (s i)
      (canonical D (c j) (c l + δ) (s j) (-e j - 1)
        (canonical D (c l) δ (s l) (-e l - 1) w)) (-e i - 1)]
  rfl

private theorem three_total_charge (D : LatticeData) (c : Fin 3 → Charge D)
    (δ : Charge D) (i j l : Fin 3)
    (hp : ([0, 1, 2] : List (Fin 3)).Perm [i, j, l]) :
    c i + (c j + (c l + δ)) = c 0 + (c 1 + (c 2 + δ)) := by
  have hs := (hp.map c).sum_eq
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hs
  simpa only [add_assoc] using congrArg (fun q : Charge D => q + δ) hs.symm

private theorem projected_word (D : LatticeData) (c : Fin 3 → Charge D)
    (s : Fin 3 → Oscillator D) (δ : Charge D) (w : Sector D δ)
    (i j l : Fin 3) (hp : ([0, 1, 2] : List (Fin 3)).Perm [i, j, l]) :
    (fun e => projection D (c 0 + (c 1 + (c 2 + δ)))
      (coefficientDistribution (labelledFields D c s) (inclusion D δ w) 1 [i, j, l] e)) =
        nestedCanonical D c s δ w i j l := by
  funext e
  rw [word_three]
  change (Finsupp.single (c i + (c j + (c l + δ)))
    (nestedCanonical D c s δ w i j l e)) (c 0 + (c 1 + (c 2 + δ))) = _
  rw [three_total_charge D c δ i j l hp, Finsupp.single_eq_same]

/-- Six original canonical three-field products, on arbitrary fourth-sector
states, have one common generally infinite power series after Q-clearing and
statewise monomial shifting. All signed multi-indices are asserted, including
below support. The common k precedes δ,w; no positivity, rank, nonsingularity,
energy grading, or assumed iterated-product/collision law is a premise.

These are the six field orders 012, 021, 102, 120, 201, 210 with their labels
fixed to u,v,t. No associator, pentagon, hexagon, or analytic convergence is claimed. -/
theorem actual_three_field_common_series
    (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) :
    let c : Fin 3 → Charge D := ![α, β, γ]
    let s : Fin 3 → Oscillator D := ![u, v, t]
    ∃ k : ℕ,
      (∀ i j : Fin 3, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c s i) (labelledFields D c s j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 3 → ℕ,
        ∃ P : MvPowerSeries (Fin 3) (Oscillator D),
        (∀ (i : Fin 3) (n : ℤ), (a i : ℤ) ≤ n → canonical D (c i) δ (s i) n w = 0) ∧
        ∀ e : Exponent 3,
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 0 1 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 0 2 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 1 0 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 1 2 0)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 2 0 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 2 1 0)
            (fun i => e i - a i) = signedExtend P e := by
  classical
  dsimp only
  let c : Fin 3 → Charge D := ![α, β, γ]
  let s : Fin 3 → Oscillator D := ![u, v, t]
  have pairLocal : ∀ i j : Fin 3, i < j →
      ∃ r : ℕ, (deltaEnd ^ r)
        (commutator (labelledFields D c s i) (labelledFields D c s j)) = 0 := by
    intro i j _
    obtain ⟨r, hr⟩ := LatticeAllStateLocality.stateField_locality D
      (inclusion D (c i) (s i)) (inclusion D (c j) (s j))
    refine ⟨r, ?_⟩
    rw [Module.End.pow_apply]
    exact hr
  have complete : ∀ i : Fin 3, i ∈ ([0, 1, 2] : List (Fin 3)) := by
    intro i
    fin_cases i <;> simp
  obtain ⟨k, hk, rest⟩ := ungraded_local_word_common_series
    (labelledFields D c s) [0, 1, 2] (by decide) complete pairLocal
  refine ⟨k, hk, ?_⟩
  intro δ w
  obtain ⟨a, C, truncation, commonCarrier⟩ := rest (inclusion D δ w)
  let f : Carrier D →ₗ[ℂ] Oscillator D := projection D (c 0 + (c 1 + (c 2 + δ)))
  let P : MvPowerSeries (Fin 3) (Oscillator D) := fun d => f (C d)
  have common (i j l : Fin 3) (hp : ([0, 1, 2] : List (Fin 3)).Perm [i, j, l])
      (e : Exponent 3) :
      polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w i j l)
        (fun m => e m - a m) = signedExtend P e := by
    have h := congrArg f (commonCarrier [i, j, l] hp e)
    rw [polynomialAction_map, signedExtend_map] at h
    change polynomialAction (clearingPolynomial 3 k)
      (fun x => projection D (c 0 + (c 1 + (c 2 + δ)))
        (coefficientDistribution (labelledFields D c s) (inclusion D δ w) 1 [i, j, l] x))
          (fun m => e m - a m) = signedExtend P e at h
    rw [projected_word D c s δ w i j l hp] at h
    exact h
  refine ⟨a, P, ?_, ?_⟩
  · intro i n hn
    change projection D (c i + δ)
      (((labelledFields D c s i)[[n]]) (inclusion D δ w)) = 0
    rw [truncation i n hn, map_zero]
  · intro e
    exact ⟨common 0 1 2 (by decide) e,
      common 0 2 1 (by decide) e,
      common 1 0 2 (by decide) e,
      common 1 2 0 (by decide) e,
      common 2 0 1 (by decide) e,
      common 2 1 0 (by decide) e⟩

#print axioms actual_three_field_common_series

end
end D5.S3.VertexAlgebra.LatticeSectorThreeFieldCommonSeries
