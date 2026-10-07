/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIFibres
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47TypeIIFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lower bounds for genuine corrected factor-tuple fibres on powered components. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIILemma41
import D5.S3.FiniteGroups.NikolovSegal.ExtractionCounting

set_option autoImplicit false

/-! Actual centreless Proposition9.1 fibre reconstruction, Part I pp223--226.
The independent retained-word solver is consumed on the actual normalized
VALUE residual. Its unextracted coordinates become actual commutator VALUES,
not unconstrained witness variables. y remains fixed before every target. -/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling CrossingKernel
universe u
variable {S I : Type u} [Group S] [Fintype S] [Fintype I] [DecidableEq I] {m q D : ℕ}

abbrev CorrectedSolution (k : Fin m → MulAut (I → S)) (y : Fin m → I → S)
    (q : ℕ) (kappa : I → S) :=
  {c : Fin m → I → S // ∀ v, orderedProduct (fun j => (c j v)⁻¹ *
    (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v}

abbrev FixedCycleSolution (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (y : Fin m → I → S) (q : ℕ) (u : ∀ j, ActualCycle (sigma j ^ q) → S) (kappa : I → S) :=
  {c : Fin m → I → S //
    (∀ j (C : ActualCycle (sigma j ^ q)), c j C.out = u j C) ∧
    ∀ v, orderedProduct (fun j => (c j v)⁻¹ *
      (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v}

/-- Count genuine factor-tuple witnesses with prescribed cycle-base scalar
parameters. The free parameters are ACTUAL unused nonbase VALUES outside
2D CONSTRUCTED extraction keys. Extraction, balance and support are derived
from the genuine cycle inequality (36), with no fibre/surjectivity premise. -/
theorem actual_connected_fixed_cycle_fibre_bound
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (root : I)
    (hreach : ∀ v, (qPowerGraph sigma q).Reachable root v)
    (hn : 2 ≤ Fintype.card I)
    (hcycle : (∑ j : Fin m, actualCycleCount (sigma j ^ q)) +
      2*Fintype.card I+2*D ≤ m*Fintype.card I)
    (htwisted : PartIITwistedProductInput S D) :
    ∀ (u : ∀ j, ActualCycle (sigma j ^ q) → S) (kappa : I → S),
      (Fintype.card S)^(m*Fintype.card I - (∑ j : Fin m, actualCycleCount (sigma j ^ q)) -
        (Fintype.card I-1)-2*D) ≤ Nat.card (FixedCycleSolution k sigma y q u kappa) := by
  classical
  let tau := fun j => sigma j ^ q
  let alpha := fun j i => correctedCycleComponent beta sigma y j i q
  have hgraph : qPowerGraph tau 1 = qPowerGraph sigma q := by
    ext v w
    simp only [tau,qPowerGraph,pow_one]
  obtain ⟨F,L,hF,hacyc,hgraph',hL,hroots,hedges⟩ := exists_value_leafOrder tau (fun _ => root)
    (by simpa only [hgraph] using hreach) (fun _ _ _ => rfl)
  let Y := valueResidualSupport tau L (fun _ => root) root
  have hpair := normalized_connected_residual_pair_count tau L hL root hroots
  have hcount := normalized_actual_variable_card tau
  have hY : Y.card = m*Fintype.card I - (∑ j : Fin m, actualCycleCount (sigma j ^ q)) -
      (Fintype.card I-1) := by dsimp [Y,tau] at *; omega
  have hbudget : Fintype.card I+2*D ≤ Y.card := by rw [hY]; omega
  intro u kappa
  let W := contractValueSystem kappa L (normalizedVertexWord tau alpha u) root
  have hsign : ∀ e s, (signedVariables W).count (e,s) = if e ∈ Y then 1 else 0 := by
    intro e s
    simpa only [W,Y,valueResidualSupport,Finset.mem_filter,Finset.mem_univ,true_and] using
      normalized_value_residual_sign_count tau alpha u kappa L hL (fun _ => root) hroots
        (fun _ _ _ => rfl) root rfl e s
  obtain ⟨P⟩ := CrossingKernel.extraction_from_owner_counts Prod.fst (Fintype.card I) D W Y
    (by intro e s; simpa only [List.count_eq_countP,_root_.beq_eq_decide] using hsign e s)
    (normalized_connected_residual_colour tau alpha u kappa L hL root hroots) hbudget
  let E := (extractedKeys P).toFinset
  have hEY : E ⊆ Y := by
    intro e he
    obtain ⟨s,hs⟩ := extractedKeys_mem P e (List.mem_toFinset.mp he)
    have hs' : (e,s) ∈ signedVariables W := hs
    have hc := List.count_pos_iff.mpr hs'
    rw [hsign] at hc
    split_ifs at hc <;> first | assumption | omega
  have hE : E.card = 2*D := ExtractionCounting.extracted_key_card P
  let U := Y \ E
  let Free := {e : Arc m I // e ∈ U}
  let Sol := FixedCycleSolution k sigma y q u kappa
  letI : Fintype Sol := Fintype.ofFinite Sol
  let restrict : Sol → (Free → S) := fun c e =>
    (c.val e.val.1 e.val.2)⁻¹ * (((k e.val.1 * MulAut.conj (y e.val.1)⁻¹)^q) (c.val e.val.1)) e.val.2
  have hsurj : Function.Surjective restrict := by
    intro rho
    let z : Arc m I → S := fun e => if he : e ∈ U then rho ⟨e,he⟩ else 1
    obtain ⟨z',hz,hretain,hfinal⟩ := ExtractionCounting.solve_extracted_word_retaining P htwisted z (kappa root)
    obtain ⟨c,hc,hvalues,hunused⟩ := corrected_value_forest_extension k sigma beta hcoord y L hL
      (fun _ => root) hroots u kappa z' (by intro v hv; subst v; exact hz)
    refine ⟨⟨c,hc,hvalues⟩,?_⟩
    funext e
    have he := Finset.mem_sdiff.mp e.prop
    have heY := (Finset.mem_filter.mp he.1).2
    have hen : e.val ∉ extractedKeys P := fun h => he.2 (List.mem_toFinset.mpr h)
    change (c e.val.1 e.val.2)⁻¹ * (((k e.val.1 * MulAut.conj (y e.val.1)⁻¹)^q) (c e.val.1)) e.val.2 = rho e
    rw [hunused e.val heY.1 heY.2.1,hretain e.val hen]
    simp only [z,dif_pos e.prop]
    congr 1
  have hh := Fintype.card_le_of_surjective restrict hsurj
  have hFree : Fintype.card Free = Y.card-2*D := by
    change Fintype.card U = _
    rw [Fintype.card_coe,Finset.card_sdiff_of_subset hEY,hE]
  rw [Fintype.card_fun,hFree] at hh
  rw [← hY]
  simpa only [Sol,Nat.card_eq_fintype_card] using hh

/-- Sum the fixed-cycle fibres. Their scalar parameters are independent and
uniquely determined by an actual tuple, so they count disjoint genuine
witnesses. This proves the centreless connected Proposition9.1 count with
the sharper loss n-1+2D, conditional only on the precise twisted PRODUCT
input and its actual cycle inequality. -/
theorem actual_connected_typeII_fibre_bound
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (root : I)
    (hreach : ∀ v, (qPowerGraph sigma q).Reachable root v)
    (hn : 2 ≤ Fintype.card I)
    (hcycle : (∑ j : Fin m, actualCycleCount (sigma j ^ q)) +
      2*Fintype.card I+2*D ≤ m*Fintype.card I)
    (htwisted : PartIITwistedProductInput S D) :
    ∀ kappa : I → S, (Fintype.card S)^(m*Fintype.card I-(Fintype.card I-1+2*D)) ≤
      Nat.card (CorrectedSolution k y q kappa) := by
  classical
  letI : ∀ j : Fin m, Fintype (ActualCycle (sigma j ^ q)) := fun _ => Fintype.ofFinite _
  let B := ∀ j, ActualCycle (sigma j ^ q) → S
  have hB : Fintype.card B = (Fintype.card S)^(∑ j : Fin m, actualCycleCount (sigma j ^ q)) := by
    simp only [B,Fintype.card_pi,Finset.prod_const,Finset.card_univ,actualCycleCount,
      Nat.card_eq_fintype_card,Finset.prod_pow_eq_pow_sum]
  intro kappa
  let Sol := CorrectedSolution k y q kappa
  let Fixed := fun u : B => FixedCycleSolution k sigma y q u kappa
  letI : Fintype Sol := Fintype.ofFinite Sol
  letI : ∀ u : B, Fintype (Fixed u) := fun _ => Fintype.ofFinite _
  let forget : (u : B) × Fixed u → Sol := fun c => ⟨c.2.val,c.2.prop.2⟩
  have hinj : Function.Injective forget := by
    rintro ⟨ua,ca⟩ ⟨ub,cb⟩ h
    have hc : ca.val = cb.val := congrArg Subtype.val h
    have hu : ua = ub := by
      funext j C
      exact (ca.prop.1 j C).symm.trans ((congrFun (congrFun hc j) C.out).trans (cb.prop.1 j C))
    subst ub
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hc))
  let E := m*Fintype.card I-(∑ j : Fin m, actualCycleCount (sigma j ^ q))-(Fintype.card I-1)-2*D
  have hlower : ∀ u : B, (Fintype.card S)^E ≤ Fintype.card (Fixed u) := by
    intro u
    simpa only [Fixed,Nat.card_eq_fintype_card] using
      actual_connected_fixed_cycle_fibre_bound k sigma beta hcoord y root hreach hn hcycle htwisted u kappa
  have hs := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset B)) => hlower u)
  have htotal := Fintype.card_le_of_injective forget hinj
  rw [Fintype.card_sigma] at htotal
  have hbound : Fintype.card B * (Fintype.card S)^E ≤ Fintype.card Sol := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using hs.trans htotal
  have hexp : (∑ j : Fin m, actualCycleCount (sigma j ^ q))+E =
      m*Fintype.card I-(Fintype.card I-1+2*D) := by dsimp [E]; omega
  rw [hB,← pow_add,hexp] at hbound
  simpa only [Sol,Nat.card_eq_fintype_card] using hbound

/-- The printed Proposition9.1 centreless loss 4Dn follows from the sharper
actual witness count. This retains actual cycle inequality (36), powered
connectivity, arbitrary genuine component automorphisms and fixed y. It does
NOT assert the central-cover/quasisimple extension or the twisted existence. -/
theorem actual_connected_proposition9_1_count
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (root : I)
    (hreach : ∀ v, (qPowerGraph sigma q).Reachable root v)
    (hn : 2 ≤ Fintype.card I) (hD : 0 < D)
    (hcycle : (∑ j : Fin m, actualCycleCount (sigma j ^ q)) +
      2*Fintype.card I+2*D ≤ m*Fintype.card I)
    (htwisted : PartIITwistedProductInput S D) (kappa : I → S) :
    (Fintype.card S)^(m*Fintype.card I) ≤
      Nat.card (CorrectedSolution k y q kappa) * (Fintype.card S)^(4*D*Fintype.card I) := by
  have hcount := actual_connected_typeII_fibre_bound k sigma beta hcoord y root hreach hn hcycle htwisted kappa
  have hcard : 1 ≤ Fintype.card S := Fintype.card_pos
  have hloss : Fintype.card I-1+2*D ≤ 4*D*Fintype.card I := by
    have hDn : Fintype.card I ≤ D*Fintype.card I := by nlinarith
    have hD2 : 2*D ≤ D*Fintype.card I := by nlinarith
    have hfour : 4*D*Fintype.card I = 4*(D*Fintype.card I) := by ring
    rw [hfour]
    omega
  have hexp : m*Fintype.card I-(Fintype.card I-1+2*D)+(Fintype.card I-1+2*D) =
      m*Fintype.card I := by omega
  calc
    _ = (Fintype.card S)^(m*Fintype.card I-(Fintype.card I-1+2*D)) *
        (Fintype.card S)^(Fintype.card I-1+2*D) := by rw [← pow_add,hexp]
    _ ≤ Nat.card (CorrectedSolution k y q kappa) * (Fintype.card S)^(4*D*Fintype.card I) :=
      Nat.mul_le_mul hcount (pow_le_pow_right' hcard hloss)

end NikolovSegal.Equation47ValueNormalization
