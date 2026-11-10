/- GID: D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/SubcubicCycles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact cyclic shared-port parameters with alternating bipartition and matching. -/

import D5.S3.Combinatorics.Graph.StarForming.SubcubicIdentificationBeta
import D5.S3.Combinatorics.Graph.StarForming.DominationComparison
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The actual even cyclic J_r of SUBCUBIC_STAR_FORMING_GAPS,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69.
The core, shared-port and graph-invariant parameters retain their distinct
roles. The cyclic restriction is positive even r, hence r at least two. -/
namespace D5.S3.Combinatorics.Graph.StarForming.SubcubicCycles
open StarFormingDissociationRefutation SubcubicIdentification
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

private theorem phase_prev (next : Equiv.Perm I) (phase : I → Bool)
    (hp : ∀ i, phase (next i)= !(phase i)) (i : I) :
    phase (next.symm i)= !(phase i) := by
  have hh := hp (next.symm i)
  rw [Equiv.apply_symm_apply] at hh
  cases h : phase i <;> cases h' : phase (next.symm i) <;> simp_all

def color (phase : I → Bool) (x : I × Fin 11) : Fin 2 :=
  if phase x.1 == decide (x.2.val<5 ∨ x.2=10) then 0 else 1

set_option maxRecDepth 8192 in
/-- Alternating cells give the actual bipartition, including both port edges. -/
theorem bipartite (next : Equiv.Perm I) (phase : I → Bool)
    (hp : ∀ i, phase (next i)= !(phase i)) : (graph next).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (color phase) ?_⟩
  rintro ⟨i,v⟩ y h
  have hm := phase_prev next phase hp i
  fin_cases v <;> cases hi : phase i <;>
    simp [graph,neighbors] at h <;>
    aesop (add simp [color,hp,hm,hi])

def mate (next : Equiv.Perm I) (phase : I → Bool) (x : I × Fin 11) : I × Fin 11 :=
  if phase x.1 then
    ![(x.1,6),(x.1,7),(next x.1,10),(x.1,8),(x.1,5),(x.1,4),
      (x.1,0),(x.1,1),(x.1,3),(x.1,10),(x.1,9)] x.2
  else
    ![(x.1,7),(x.1,9),(x.1,6),(x.1,8),(x.1,5),(x.1,4),
      (x.1,2),(x.1,0),(x.1,3),(x.1,1),(next.symm x.1,2)] x.2

private theorem mate_facts (next : Equiv.Perm I) (phase : I → Bool)
    (hp : ∀ i, phase (next i)= !(phase i)) :
    Function.Involutive (mate next phase) ∧ ∀ x, (graph next).Adj x (mate next phase x) := by
  constructor
  · rintro ⟨i,v⟩
    have hm := phase_prev next phase hp i
    fin_cases v <;> cases hi : phase i <;> simp [mate,hi,hp,hm]
  · rintro ⟨i,v⟩
    fin_cases v <;> cases hi : phase i <;> simp [mate,graph,neighbors,hi]

/-- The actual displayed perfect matching bounds every independent selection;
the two bipartition sides supply the reverse half-order bound. -/
theorem alpha_half (next : Equiv.Perm I) (phase : I → Bool)
    (hp : ∀ i, phase (next i)= !(phase i)) :
    2*(graph next).indepNum=11*Fintype.card I := by
  classical
  let G := graph next
  have hm := mate_facts next phase hp
  have hu : 2*G.indepNum≤Fintype.card (I × Fin 11) := by
    obtain ⟨J,hJ⟩ := G.maximumIndepSet_exists
    let K := J.image (mate next phase)
    have hk : K.card=J.card := Finset.card_image_of_injective J hm.1.injective
    have hd : Disjoint J K := by
      apply Finset.disjoint_left.mpr
      intro v hv hkv
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hkv
      have he := hm.2 u
      exact hJ.isIndepSet hu hv (G.ne_of_adj he) he
    have hc := Finset.card_le_univ (J∪K)
    rw [Finset.card_union_of_disjoint hd,hk] at hc
    rw [G.maximumIndepSet_card_eq_indepNum J hJ] at hc
    omega
  obtain ⟨c⟩ := bipartite next phase hp
  let L := Finset.univ.filter (fun v => c v=(0 : Fin 2))
  let R := Finset.univ.filter (fun v => c v=(1 : Fin 2))
  have hi (k : Fin 2) : G.IsIndepSet
      ((Finset.univ.filter (fun v => c v=k) : Finset (I × Fin 11)) : Set (I × Fin 11)) := by
    intro v hv w hw _ h
    exact c.valid h ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)
  have hl : L.card≤G.indepNum := (hi 0).card_le_indepNum
  have hr : R.card≤G.indepNum := (hi 1).card_le_indepNum
  have he : L∪R=Finset.univ := by
    ext v
    have hc : c v=0 ∨ c v=1 := by omega
    simp [L,R,hc]
  have hd : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have h0 := (Finset.mem_filter.mp hv).2
    have h1 := (Finset.mem_filter.mp hw).2
    have : (0 : Fin 2)=1 := h0.symm.trans h1
    exact (by decide : (0 : Fin 2)≠1) this
  have hc := Finset.card_union_of_disjoint hd
  rw [he,Finset.card_univ] at hc
  simp only [Fintype.card_prod,Fintype.card_fin] at hu hc
  change 2*G.indepNum=11*Fintype.card I
  omega

/-- Counts on the actual graph include each identified port once. -/
theorem degree_counts (next : Equiv.Perm I) :
    (Finset.univ.filter (fun x => DegreeCapacity.degree (graph next) x=2)).card=5*Fintype.card I ∧
    (Finset.univ.filter (fun x => DegreeCapacity.degree (graph next) x=3)).card=6*Fintype.card I := by
  classical
  constructor
  all_goals
    rw [ClosedModule.card_fibers]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,degrees]
  · have h : (Finset.univ.filter (fun v : Fin 11 =>
        (if v=3 ∨ v=4 ∨ v=6 ∨ v=7 ∨ v=10 then 2 else 3)=2)).card=5 := by decide +kernel
    simp only [h,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm]
  · have h : (Finset.univ.filter (fun v : Fin 11 =>
        (if v=3 ∨ v=4 ∨ v=6 ∨ v=7 ∨ v=10 then 2 else 3)=3)).card=6 := by decide +kernel
    simp only [h,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm]

/-- The original cyclic identification has fourteen actual edges per cell. -/
theorem edge_count (next : Equiv.Perm I) : (graph next).edgeFinset.card=14*Fintype.card I := by
  classical
  have he := (graph next).sum_degrees_eq_twice_card_edges
  have hd (x : I × Fin 11) : (graph next).degree x=DegreeCapacity.degree (graph next) x := by
    unfold SimpleGraph.degree DegreeCapacity.degree
    congr 1
    ext w
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_filter,Finset.mem_univ,true_and]
  simp_rw [hd] at he
  rw [Fintype.sum_prod_type] at he
  have hlocal (i : I) : ∑ v : Fin 11, DegreeCapacity.degree (graph next) (i,v)=28 := by
    simp only [degrees]
    decide +kernel
  simp_rw [hlocal] at he
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at he
  omega

def cyclicPhase {r : ℕ} (i : Fin r) : Bool := decide (i.val%2=0)

/-- Evenness is used at the wrap edge, rather than dropped from the domain. -/
theorem cyclic_phase (r : ℕ) (hr : 0<r) (he : Even r) :
    ∀ i : Fin r, cyclicPhase (finRotate r i)= !(cyclicPhase i) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  intro i
  have hmod : (n+1)%2=0 := Nat.even_iff.mp he
  have hv : (finRotate (n+1) i).val%2=0 ↔ ¬ i.val%2=0 := by
    rw [coe_finRotate]
    split_ifs with h
    · subst i
      simp only [Fin.val_last, Nat.zero_mod, true_iff]
      omega
    · have hil := i.isLt
      omega
  simpa only [cyclicPhase,← decide_not,decide_eq_decide] using hv

/-- Exact actual SF, beta, Gamma and alpha on every positive even cyclic size. -/
theorem cyclic_parameters (r : ℕ) (hr : 0<r) (he : Even r) :
    let G := graph (finRotate r)
    Fintype.card (Fin r × Fin 11)=11*r ∧ G.edgeFinset.card=14*r ∧
    SF G 2=7*r ∧ 2*beta G 2=13*r ∧ 2*G.indepNum=11*r ∧
    2*DominationComparison.Gamma G=11*r ∧ 2*(SF G 2-beta G 2)=r := by
  classical
  have hp := cyclic_phase r hr he
  have nf : ∀ i : Fin r, finRotate r i≠i := by
    intro i h
    have hh := hp i
    rw [h] at hh
    cases cyclicPhase i <;> simp at hh
  have hb := SubcubicIdentificationBeta.beta_exact (finRotate r) nf cyclicPhase hp
  have hs := sf_exact (finRotate r)
  have ha := alpha_half (finRotate r) cyclicPhase hp
  have hg := DominationComparison.gamma_eq_alpha (graph (finRotate r))
    (bipartite (finRotate r) cyclicPhase hp)
  have hm := edge_count (finRotate r)
  simp only [Fintype.card_fin] at hb hs ha hm
  refine ⟨by simp [Nat.mul_comm],hm,hs,hb,ha,?_,?_⟩ <;> omega

end D5.S3.Combinatorics.Graph.StarForming.SubcubicCycles
