/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldCommonSeries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldCommonSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Twenty-four actual descendant four-field words share an infinite vector series. -/

import D5.S3.VertexAlgebra.FormalSeries.UngradedLocalWordSeries
import D5.S3.VertexAlgebra.Sectors.LatticeSectorBorcherds

/-!
The original canonical normalization and Bakalov--Kac, Matsuo--Nagatomo and
Carnahan supplier attributions are retained. This is the sector projection
of the existing arbitrary-N ungraded local-word supplier.
proof_shape: actual_four_field_common_series: bind-only
Consumed by actual_four_field_inner_iterate_transport; this adapter is not
new collision content. Labels remain attached to their original variables.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorFourFieldCommonSeries

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner UniformGradedLocalCorrelator UngradedLocalWordSeries
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

/-- Four labelled actual fields, including arbitrary oscillator descendants.
Only the labels are distinct; charges and fields may repeat. -/
def labelledFields (D : LatticeData) (c : Fin 4 → Charge D)
    (s : Fin 4 → Oscillator D) : Fin 4 → VertexOperator ℂ (Carrier D) :=
  fun i => Y D (inclusion D (c i) (s i))

/-- The literal four nested canonical intertwiners, with exponents attached
to their original field labels, for an arbitrary fifth sector input. -/
def nestedCanonical (D : LatticeData) (c : Fin 4 → Charge D)
    (s : Fin 4 → Oscillator D) (δ : Charge D) (w : Sector D δ)
    (i j l m : Fin 4) (e : Exponent 4) : Oscillator D :=
  canonical D (c i) (c j + (c l + (c m + δ))) (s i) (-e i - 1)
    (canonical D (c j) (c l + (c m + δ)) (s j) (-e j - 1)
      (canonical D (c l) (c m + δ) (s l) (-e l - 1)
        (canonical D (c m) δ (s m) (-e m - 1) w)))

private theorem word_four (D : LatticeData) (c : Fin 4 → Charge D)
    (s : Fin 4 → Oscillator D) (δ : Charge D) (w : Sector D δ)
    (i j l m : Fin 4) (e : Exponent 4) :
    coefficientDistribution (labelledFields D c s) (inclusion D δ w) 1 [i,j,l,m] e =
      inclusion D (c i + (c j + (c l + (c m + δ))))
        (nestedCanonical D c s δ w i j l m e) := by
  change ((Y D (inclusion D (c i) (s i)))[[-e i - 1]])
    (((Y D (inclusion D (c j) (s j)))[[-e j - 1]])
      (((Y D (inclusion D (c l) (s l)))[[-e l - 1]])
        (((Y D (inclusion D (c m) (s m)))[[-e m - 1]]) (inclusion D δ w)))) = _
  rw [← inclusion_canonical D (c m) δ (s m) w (-e m - 1),
    ← inclusion_canonical D (c l) (c m + δ) (s l)
      (canonical D (c m) δ (s m) (-e m - 1) w) (-e l - 1),
    ← inclusion_canonical D (c j) (c l + (c m + δ)) (s j)
      (canonical D (c l) (c m + δ) (s l) (-e l - 1)
        (canonical D (c m) δ (s m) (-e m - 1) w)) (-e j - 1),
    ← inclusion_canonical D (c i) (c j + (c l + (c m + δ))) (s i)
      (canonical D (c j) (c l + (c m + δ)) (s j) (-e j - 1)
        (canonical D (c l) (c m + δ) (s l) (-e l - 1)
          (canonical D (c m) δ (s m) (-e m - 1) w))) (-e i - 1)]
  rfl

private theorem four_total_charge (D : LatticeData) (c : Fin 4 → Charge D)
    (δ : Charge D) (i j l m : Fin 4)
    (hp : ([0, 1, 2, 3] : List (Fin 4)).Perm [i, j, l, m]) :
    c i + (c j + (c l + (c m + δ))) = c 0 + (c 1 + (c 2 + (c 3 + δ))) := by
  have hs := (hp.map c).sum_eq
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hs
  simpa only [add_assoc] using congrArg (fun q : Charge D => q + δ) hs.symm

private theorem projected_word (D : LatticeData) (c : Fin 4 → Charge D)
    (s : Fin 4 → Oscillator D) (δ : Charge D) (w : Sector D δ)
    (i j l m : Fin 4) (hp : ([0, 1, 2, 3] : List (Fin 4)).Perm [i, j, l, m]) :
    (fun e => projection D (c 0 + (c 1 + (c 2 + (c 3 + δ))))
      (coefficientDistribution (labelledFields D c s) (inclusion D δ w) 1 [i, j, l, m] e)) =
        nestedCanonical D c s δ w i j l m := by
  funext e
  rw [word_four]
  change (Finsupp.single (c i + (c j + (c l + (c m + δ))))
    (nestedCanonical D c s δ w i j l m e)) (c 0 + (c 1 + (c 2 + (c 3 + δ)))) = _
  rw [four_total_charge D c δ i j l m hp, Finsupp.single_eq_same]

/-- All twenty-four labelled canonical four-field products share one
infinite vector power series. The four truncations are on the original w,
and the locality order precedes the choice of its charge and state. -/
theorem actual_four_field_common_series
    (D : LatticeData) (α β γ η : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η) :
    let c : Fin 4 → Charge D := ![α, β, γ, η]
    let s : Fin 4 → Oscillator D := ![u, v, t, q]
    ∃ k : ℕ,
      (∀ i j : Fin 4, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c s i) (labelledFields D c s j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 4 → ℕ,
        ∃ P : MvPowerSeries (Fin 4) (Oscillator D),
        (∀ (i : Fin 4) (n : ℤ), (a i : ℤ) ≤ n → canonical D (c i) δ (s i) n w = 0) ∧
        ∀ (i j l m : Fin 4), ([0,1,2,3] : List (Fin 4)).Perm [i,j,l,m] →
          ∀ e : Exponent 4,
          polynomialAction (clearingPolynomial 4 k) (nestedCanonical D c s δ w i j l m)
            (fun n => e n - a n) = signedExtend P e := by
  classical
  dsimp only
  let c : Fin 4 → Charge D := ![α, β, γ, η]
  let s : Fin 4 → Oscillator D := ![u, v, t, q]
  have pairLocal : ∀ i j : Fin 4, i < j →
      ∃ r : ℕ, (deltaEnd ^ r)
        (commutator (labelledFields D c s i) (labelledFields D c s j)) = 0 := by
    intro i j _
    obtain ⟨r, hr⟩ := LatticeAllStateLocality.stateField_locality D
      (inclusion D (c i) (s i)) (inclusion D (c j) (s j))
    refine ⟨r, ?_⟩
    rw [Module.End.pow_apply]
    exact hr
  have complete : ∀ i : Fin 4, i ∈ ([0, 1, 2, 3] : List (Fin 4)) := by
    intro i
    fin_cases i <;> simp
  obtain ⟨k, hk, rest⟩ := ungraded_local_word_common_series
    (labelledFields D c s) [0, 1, 2, 3] (by decide) complete pairLocal
  refine ⟨k, hk, ?_⟩
  intro δ w
  obtain ⟨a, C, truncation, commonCarrier⟩ := rest (inclusion D δ w)
  let f : Carrier D →ₗ[ℂ] Oscillator D := projection D (c 0 + (c 1 + (c 2 + (c 3 + δ))))
  let P : MvPowerSeries (Fin 4) (Oscillator D) := fun d => f (C d)
  have common (i j l m : Fin 4) (hp : ([0, 1, 2, 3] : List (Fin 4)).Perm [i, j, l, m])
      (e : Exponent 4) :
      polynomialAction (clearingPolynomial 4 k) (nestedCanonical D c s δ w i j l m)
        (fun m => e m - a m) = signedExtend P e := by
    have h := congrArg f (commonCarrier [i, j, l, m] hp e)
    rw [polynomialAction_map, signedExtend_map] at h
    change polynomialAction (clearingPolynomial 4 k)
      (fun x => projection D (c 0 + (c 1 + (c 2 + (c 3 + δ))))
        (coefficientDistribution (labelledFields D c s) (inclusion D δ w) 1 [i, j, l, m] x))
          (fun m => e m - a m) = signedExtend P e at h
    rw [projected_word D c s δ w i j l m hp] at h
    exact h
  refine ⟨a, P, ?_, ?_⟩
  · intro i n hn
    change projection D (c i + δ)
      (((labelledFields D c s i)[[n]]) (inclusion D δ w)) = 0
    rw [truncation i n hn, map_zero]
  · intro i j l m hp e
    exact common i j l m hp e

#print axioms actual_four_field_common_series

end
end D5.S3.VertexAlgebra.LatticeSectorFourFieldCommonSeries
