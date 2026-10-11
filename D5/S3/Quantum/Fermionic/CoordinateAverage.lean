/- GID: D5/S3/Quantum/Fermionic/CoordinateAverage
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/CoordinateAverage
   mirror-E: none(waiver:general-edge-Clifford-identification)
   anchors: []
   utility: none
   digest: The literal unordered edge average equals the flat coordinate Clifford operator. -/

/-
coordinate_average:
  proof_shape: content
  escape_witness: an explicit edge-and-orientation bijection counts each coordinate
    interaction twice in the dense Clifford sum, fixing its normalization.
admission_basis: escape-witness
Same-delivery inlined content: CoordinateEdgeHamiltonian, CoordinateCliffordSpectrum, and local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  GID: D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  GID: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount
    statement_id: sha256:97804cfc85a668f345a5b3e2421ba02e5e6203f36590508faccac8726341bc0a
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator
    statement_id: sha256:d0e241c65c207456599a205d965adefde23f6764456a0c5a832a08a676fadfb3
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.Local
    statement_id: sha256:cea3034ad5d4c2d36ac899cc7964a23cdad5b9a52b0410ee01f4b03ffd41f349
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fermionWord
    statement_id: sha256:d1484b5db3ace7148c685690abf5667976f26043e824bad34ea4385d5015100d
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC
    statement_id: sha256:e5eb14acc0a2901b62190a83ed2543f27309f7f32708edd35fa0376362ebfe97
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_CAR
    statement_id: sha256:91a39cca0cc0155aec0a40a8280d10bd356a0d091f81f8031b64299b1ade63de
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_anticomm_of_lt
    statement_id: sha256:1db13273a320d9215f5583b5d1bcd5cf5cff7952171e37a663fc509057aaacd4
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_mixed_anticomm_of_lt
    statement_id: sha256:eb93c9ae1da812ac8631c45850a4bd5f0d160da82cbfe9ad9d4377f14362f664
  GID: D5/S3/Quantum/Dynamics/ClauseHamiltonian.Assignment
    statement_id: sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
computational_content.kind: none; arbitrary vertex enumerations and mode counts.
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15194.
-/

import D5.S3.Quantum.Fermionic.CoordinateEdgeHamiltonian
import D5.S3.Quantum.Fermionic.CoordinateCliffordSpectrum
open Matrix
open scoped BigOperators
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.Fermionic.CoordinateEdgeHamiltonian
open D5.S3.Quantum.Fermionic.CompleteCartesianGraph
open D5.S3.Quantum.Fermionic.ConferenceMatrices
open D5.S3.Quantum.Fermionic.CoordinateCliffordSpectrum
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier
noncomputable section

namespace D5.S3.Quantum.Fermionic.CoordinateAverage

open Classical in
theorem coordinate_average {n q m : ℕ} (r : ℕ) (e : Fin n ≃ (Fin q → Index r))
    (a : Fin q ≃ Fin m × Bool) :
    let G := (coordinateGraph q (Index r)).comap e
    let A := (coordinateSkew q r).submatrix (fun p : Fin n × Fin q => (e p.1,p.2))
      (fun p : Fin n × Fin q => (e p.1,p.2))
    let gamma := fun p : Fin n × Fin q =>
      majorana (finProdFinEquiv (p.1,(a p.2).1)) (a p.2).2
    CStarMatrix.ofMatrix.symm (averagedHamiltonian G (coordinateCoupling r e a)) =
      (G.edgeFinset.card : ℝ)⁻¹ • ((Complex.I/2 : ℂ) •
        ∑ p, ∑ t, (A p t : ℂ) • (gamma p * gamma t)) := by
  classical
  have hsum
    (G : SimpleGraph (Fin n)) (F : Fin n → Fin n → Matrix (Assignment (n*m)) (Assignment (n*m)) ℂ) (hF : ∀ v w, F v w = F w v)
    (hz : ∀ v w, ¬ G.Adj v w → F v w = 0) :
    (2 : ℕ) • (∑ z : G.edgeSet, F z.val.out.1 z.val.out.2) = ∑ v, ∑ w, F v w := by
    classical
    let h (z : G.edgeSet) : G.Adj z.val.out.1 z.val.out.2 := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.mk, z.val.out_eq]
      exact z.property
    let d (z : G.edgeSet) : G.Dart := ⟨z.val.out,h z⟩
    have hd (z : G.edgeSet) : (d z).edge = z.val := z.val.out_eq
    let f : G.edgeSet × Bool → G.Dart := fun p => if p.2 then (d p.1).symm else d p.1
    have hbij : Function.Bijective f := by
      constructor
      · intro p t heq
        have hed : p.1 = t.1 := by
          apply Subtype.ext
          have hh := congrArg SimpleGraph.Dart.edge heq
          simpa only [f,apply_ite,SimpleGraph.Dart.edge_symm,hd,ite_self] using hh
        rcases p with ⟨z,b⟩
        rcases t with ⟨u,c⟩
        change z = u at hed
        subst u
        have hb : b = c := by
          cases b <;> cases c
          · rfl
          · exact False.elim ((d z).symm_ne (by simpa [f] using heq.symm))
          · exact False.elim ((d z).symm_ne (by simpa [f] using heq))
          · rfl
        subst c
        rfl
      · intro a
        let z : G.edgeSet := ⟨a.edge,a.edge_mem⟩
        have hh : a = d z ∨ a = (d z).symm :=
          (SimpleGraph.dart_edge_eq_iff a (d z)).mp (hd z).symm
        rcases hh with hh | hh
        · exact ⟨(z,false),hh.symm⟩
        · exact ⟨(z,true),hh.symm⟩
    have he : (∑ a : G.Dart, F a.fst a.snd) =
        ∑ p : G.edgeSet × Bool, F (f p).fst (f p).snd := by
      exact (Equiv.ofBijective f hbij).sum_comp (fun a => F a.fst a.snd) |>.symm
    have he2 : (∑ a : G.Dart, F a.fst a.snd) =
        2 • (∑ z : G.edgeSet, F z.val.out.1 z.val.out.2) := by
      rw [he,Fintype.sum_prod_type]
      simp only [Fintype.sum_bool,f,Bool.false_eq_true,if_false,if_true]
      change (∑ z : G.edgeSet, (F (z.val.out.2) (z.val.out.1) + F (z.val.out.1) (z.val.out.2))) = _
      simp_rw [← hF]
      rw [Finset.sum_add_distrib,two_nsmul]
    rw [← he2]
    let g : G.Dart ≃ {p : Fin n × Fin n // G.Adj p.1 p.2} :=
      { toFun := fun a => ⟨a.toProd,a.adj⟩
        invFun := fun a => ⟨a.val,a.property⟩
        left_inv := fun a => by cases a; rfl
        right_inv := fun a => by cases a; rfl }
    rw [← g.symm.sum_comp (fun a => F a.fst a.snd)]
    change (∑ a : {p : Fin n × Fin n // G.Adj p.1 p.2}, F a.val.1 a.val.2) = _
    have hc : (∑ a : {p : Fin n × Fin n // ¬ G.Adj p.1 p.2}, F a.val.1 a.val.2) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact hz _ _ a.property
    have hh := Fintype.sum_subtype_add_sum_subtype (fun p : Fin n × Fin n => G.Adj p.1 p.2)
      (fun p : Fin n × Fin n => F p.1 p.2)
    rw [hc,add_zero,Fintype.sum_prod_type] at hh
    exact hh
  let G := (coordinateGraph q (Index r)).comap e
  let A := (coordinateSkew q r).submatrix (fun p : Fin n × Fin q => (e p.1,p.2))
    (fun p : Fin n × Fin q => (e p.1,p.2))
  let gamma := fun p : Fin n × Fin q =>
    majorana (finProdFinEquiv (p.1,(a p.2).1)) (a p.2).2
  let F (v w : Fin n) := Complex.I • ∑ t : Fin q,
    (A (v,t) (w,t) : ℂ) • (gamma (v,t) * gamma (w,t))
  have hz (v w : Fin n) (hn : ¬ G.Adj v w) : F v w = 0 := by
    dsimp only [F]
    rw [show (∑ t : Fin q, (A (v,t) (w,t) : ℂ) •
      (gamma (v,t) * gamma (w,t))) = 0 by
      apply Finset.sum_eq_zero
      intro t _
      have ha : A (v,t) (w,t) = 0 := by
        change (if t = t ∧ ∀ b, b ≠ t → e v b = e w b
          then (conference r (e v t) (e w t) : ℝ) else 0) = 0
        by_cases hh : ∀ b, b ≠ t → e v b = e w b
        · simp only [ite_true,true_and,hh,if_true]
          have heq : e v t = e w t := by
            by_contra heq
            exact hn ⟨t,heq,hh⟩
          rw [heq,(conference_properties r).2.2.1]
          norm_num
        · simp [hh]
      rw [ha,Complex.ofReal_zero,zero_smul]]
    simp
  have hF (v w : Fin n) : F v w = F w v := by
    by_cases hvw : v = w
    · subst w; rfl
    · dsimp only [F]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      have hcoeff : A (w,t) (v,t) = -A (v,t) (w,t) := by
        exact congrArg (fun M => M (e v,t) (e w,t)) (coordinate_skew_flat q r).1
      have hne : (finProdFinEquiv (v,(a t).1),(a t).2) ≠
          (finProdFinEquiv (w,(a t).1),(a t).2) := by
        intro h
        exact hvw (congrArg Prod.fst (finProdFinEquiv.injective (congrArg Prod.fst h)))
      have hc := (majorana_clifford_and_parity (n*m)).2.2.2.1
        (finProdFinEquiv (w,(a t).1),(a t).2)
        (finProdFinEquiv (v,(a t).1),(a t).2)
      rw [if_neg (Ne.symm hne)] at hc
      have hanti : gamma (w,t) * gamma (v,t) = -(gamma (v,t) * gamma (w,t)) :=
        eq_neg_of_add_eq_zero_left hc
      rw [hcoeff,Complex.ofReal_neg,hanti,neg_smul,smul_neg,neg_neg]
  have hedge (z : G.edgeSet) : CStarMatrix.ofMatrix.symm
      (quadraticEdge z.val.out.1 z.val.out.2 (coordinateCoupling r e a z)) =
      F z.val.out.1 z.val.out.2 := by
    change (Complex.I • ∑ p : Fin m × Bool, ∑ u : Fin m × Bool,
      (coordinateCoupling r e a z p u : ℂ) •
        (majorana (finProdFinEquiv (z.val.out.1,p.1)) p.2 *
          majorana (finProdFinEquiv (z.val.out.2,u.1)) u.2)) = _
    simp only [coordinateCoupling,ite_and,apply_ite,Complex.ofReal_zero,
      ite_smul,zero_smul,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    dsimp only [F]
    rw [← a.sum_comp]
    simp only [Equiv.symm_apply_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    by_cases hh : ∀ b, b ≠ t → e z.val.out.1 b = e z.val.out.2 b
    · simp [A,coordinateSkew,gamma,hh]
      rfl
    · simp [A,coordinateSkew,gamma,hh]
  have hdense : (Complex.I : ℂ) •
      (∑ p : Fin n × Fin q, ∑ t : Fin n × Fin q, (A p t : ℂ) • (gamma p * gamma t)) =
        ∑ v, ∑ w, F v w := by
    simp only [Fintype.sum_prod_type]
    simp_rw [Finset.sum_comm (f := fun b : Fin q => fun w : Fin n =>
      ∑ t : Fin q, (A (_,b) (w,t) : ℂ) • (gamma (_,b) * gamma (w,t)))]
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    dsimp only [F]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.smul_sum]
    congr 1
    apply Finset.sum_eq_single b
    · intro t _ htb
      have ha : A (v,b) (w,t) = 0 := by simp [A,coordinateSkew,Ne.symm htb]
      rw [ha,Complex.ofReal_zero,zero_smul]
    · simp
  have hs := hsum G F hF hz
  change (G.edgeFinset.card : ℝ)⁻¹ •
    (∑ z : G.edgeSet, CStarMatrix.ofMatrix.symm
      (quadraticEdge z.val.out.1 z.val.out.2 (coordinateCoupling r e a z))) =
        (G.edgeFinset.card : ℝ)⁻¹ • ((Complex.I/2 : ℂ) •
          ∑ p, ∑ t, (A p t : ℂ) • (gamma p * gamma t))
  congr 1
  simp only [hedge]
  have hh := congrArg (fun X : Matrix (Assignment (n*m)) (Assignment (n*m)) ℂ =>
    (1/2 : ℂ) • X) hs
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul] at hh
  norm_num only [Nat.cast_ofNat,show (1/2 : ℂ)*2=1 by norm_num,one_smul] at hh
  rw [← hdense,smul_smul] at hh
  convert hh using 1 <;> congr 1 <;> ring


end D5.S3.Quantum.Fermionic.CoordinateAverage
