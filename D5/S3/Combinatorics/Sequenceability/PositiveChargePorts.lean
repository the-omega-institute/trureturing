/- GID: D5/S3/Combinatorics/Sequenceability/PositiveChargePorts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PositiveChargePorts
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original blue ports lift a directed spanning cycle to a literal all-coordinate word avoiding every complete Boolean row. -/

import D5.S3.Combinatorics.Sequenceability.PositiveChargePortGeometry
import D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton

/-! Original-coordinate port cycles and interval-avoiding words. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Sequenceability.PositiveChargePorts
open Finset
open scoped Classical
open D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
open D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton
universe u
variable {X : Type u} [DecidableEq X]

variable {M : Submodule ℤ (X → ℤ)} {Ω : Finset X} {q : X}

/-- The cycle data is literal and finite. Entries are in REVERSE cyclic order,
starting at a: (a,xi_r),(t_r,xi_(r-1)),...,(t_2,xi_1).
Step e f records f.terminal -> e.terminal using e.port itself. Closing the
chain records the remaining arc from a. B witnesses are NOT required distinct.
exists_portCycle below supplies this structure from the actual strongly
connected semicomplete relation; it is not a hidden typeclass or premise. -/
def PortStep (G : Geometry M Ω q) (e f : Finset X × X) : Prop :=
  ∃ b ∈ G.B, neighborhood M Ω e.2 = {e.1,b} ∧
    f.1 ∈ terminalNeighbors M Ω q b

structure PortCycle (G : Geometry M Ω q) (Blue : Finset X) (a : Finset X) where
  first : Finset X × X
  tail : List (Finset X × X)
  first_terminal : first.1 = a
  terminals_nodup : ((first :: tail).map Prod.fst).Nodup
  terminals_cover : ((first :: tail).map Prod.fst).toFinset = neighborhood M Ω q
  port_blue : ∀ e ∈ first :: tail, e.2 ∈ Blue
  port_incidence : ∀ e ∈ first :: tail, ∃ b ∈ G.B,
    neighborhood M Ω e.2 = {e.1,b}
  steps : List.IsChain (PortStep G) ((first :: tail) ++ [first])


/-- Lift an actual reverse directed path to original blue ports, choosing the
port at each terminal from its outgoing edge in reverse order. The last step
works for every pair whose terminal is c, so the same construction closes at
its first pair. No distinctness of B witnesses is assumed or needed. -/
private theorem lift_port_path (G : Geometry M Ω q) {Blue : Finset X}
    {t c : Finset X} {l : List (Finset X)}
    (hc : List.IsChain (fun s t => arc G Blue t s) (t :: (l ++ [c]))) :
    ∃ (e : Finset X × X) (es : List (Finset X × X)),
      e.1 = t ∧ es.map Prod.fst = l ∧
      (∀ f ∈ e :: es, f.2 ∈ Blue) ∧
      (∀ f ∈ e :: es, ∃ b ∈ G.B, neighborhood M Ω f.2 = {f.1,b}) ∧
      ∀ f : Finset X × X, f.1 = c →
        List.IsChain (PortStep G) ((e :: es) ++ [f]) := by
  induction l generalizing t with
  | nil =>
    obtain ⟨hcT,htT,hct,b,hb,hcb,x,hxt,hxB⟩ := hc.rel
    have hx := Finset.mem_inter.mp hxt
    have hxN := G.pair b hb t htT x hx.1 hx.2
    refine ⟨(t,x),[],rfl,rfl,?_,?_,?_⟩
    · intro f hf
      have hf' : f = (t,x) := by simpa using hf
      simpa [hf'] using hxB
    · intro f hf
      have hf' : f = (t,x) := by simpa using hf
      exact ⟨b,hb,by simpa [hf'] using hxN⟩
    · intro f hf
      apply List.isChain_pair.mpr
      exact ⟨b,hb,hxN,by simpa [hf] using hcb⟩
  | cons s l ih =>
    obtain ⟨hsT,htT,hst,b,hb,hsb,x,hxt,hxB⟩ := hc.rel
    have hx := Finset.mem_inter.mp hxt
    have hxN := G.pair b hb t htT x hx.1 hx.2
    obtain ⟨e,es,he,hes,hblue,hinc,hsteps⟩ := ih hc.tail
    refine ⟨(t,x),e :: es,rfl,?_,?_,?_,?_⟩
    · simpa only [List.map_cons,he,hes]
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hxB
      · exact hblue f hf
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨b,hb,hxN⟩
      · exact hinc f hf
    · intro f hf
      apply List.IsChain.cons_cons
      · exact ⟨b,hb,hxN,by simpa [he] using hsb⟩
      · exact hsteps f hf

/-- Construct the actual original-port Hamilton cycle from the proved native
semicompleteness and strong connectivity. Applying the generic theorem to the
reverse relation gives exactly the orientation required by PortStep. Blue IDs
are chosen from ORIGINAL arc witnesses. Their distinctness is subsequently
proved by the existing PortCycle.ports_nodup from distinct terminal endpoints.
-/
theorem exists_portCycle (G : Geometry M Ω q) (b0 a z u : Finset X)
    (rank : Finset X → ℕ) (hb0 : b0 ∈ G.B)
    (ha : a ∈ terminalNeighbors M Ω q b0)
    (hz : z ∈ terminalNeighbors M Ω q b0) (haz : a ≠ z)
    (hu : u ∈ neighborhood M Ω q) (hu0 : u ∉ terminalNeighbors M Ω q b0)
    (hrank : ∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q,
      rank s = rank t → s = t)
    (hmin : ∀ t ∈ neighborhood M Ω q, rank a ≤ rank t)
    (hmax : ∀ t ∈ neighborhood M Ω q, rank t ≤ rank z)
    {K : Finset X} (hKB : ∀ b ∈ G.B, Disjoint K b) :
    Nonempty (PortCycle G (blue G b0 z rank K) a) := by
  let T := neighborhood M Ω q
  let D := fun s t : Finset X => arc G (blue G b0 z rank K) t s
  have haT : a ∈ T := (mem_terminalNeighbors.mp ha).1
  have hzT : z ∈ T := (mem_terminalNeighbors.mp hz).1
  have hsize : 2 ≤ T.card := by
    have h := Finset.one_lt_card.mpr ⟨a,haT,z,hzT,haz⟩
    omega
  have hD : ∀ {s t}, D s t → s ∈ T ∧ t ∈ T := by
    intro s t h
    exact ⟨h.2.1,h.1⟩
  have hsemi : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → D s t ∨ D t s := by
    intro s hs t ht hst
    rcases semicomplete G b0 z rank hrank hKB hs ht hst with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hstrong : ∀ s ∈ T, ∀ t ∈ T, Relation.ReflTransGen D s t := by
    intro s hs t ht
    exact (Relation.reflTransGen_swap
      (r := arc G (blue G b0 z rank K)) (a := s) (b := t)).mpr
      (stronglyConnected G b0 a z u rank hb0 ha hz haz hu hu0
        hrank hmin hmax hKB t ht s hs)
  obtain ⟨l,hn,hcover,_hlen,hchain⟩ :=
    finite_semicomplete_hamilton T D hD hsize hsemi hstrong a haT
  obtain ⟨e,es,he,hes,hblue,hinc,hsteps⟩ := lift_port_path G hchain
  have hmap : (e :: es).map Prod.fst = a :: l := by
    simp only [List.map_cons,he,hes]
  exact ⟨{
    first := e
    tail := es
    first_terminal := he
    terminals_nodup := by rw [hmap]; exact hn
    terminals_cover := by rw [hmap]; exact hcover
    port_blue := hblue
    port_incidence := hinc
    steps := hsteps e he
  }⟩

theorem PortCycle.terminal_mem (G : Geometry M Ω q)
    {Blue : Finset X} {a : Finset X} (C : PortCycle G Blue a)
    {e : Finset X × X} (he : e ∈ C.first :: C.tail) :
    e.1 ∈ neighborhood M Ω q := by
  rw [← C.terminals_cover]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)

/-- Distinct ORIGINAL blue IDs follow from distinct terminal endpoints alone. -/
theorem PortCycle.ports_nodup (G : Geometry M Ω q)
    {Blue : Finset X} {a : Finset X} (C : PortCycle G Blue a) :
    ((C.first :: C.tail).map Prod.snd).Nodup := by
  have hn : (C.first :: C.tail).Nodup := C.terminals_nodup.of_map Prod.fst
  apply hn.map_on
  intro e he f hf hef
  obtain ⟨b,hb,heN⟩ := C.port_incidence e he
  obtain ⟨d,hd,hfN⟩ := C.port_incidence f hf
  have hfN' : neighborhood M Ω e.2 = {f.1,d} := hef.symm ▸ hfN
  have hfst := (G.pair_unique hb hd (C.terminal_mem G he)
    (C.terminal_mem G hf) heN hfN').1
  exact Prod.ext hfst hef

/-- An interval joining both sides of a separator contains the separator. -/
private theorem infix_crosses {w t L R : List X} {c x y : X}
    (hn : w.Nodup) (ht : t <:+: w) (he : w = L ++ c :: R)
    (hxL : x ∈ L) (hyR : y ∈ R) (hxt : x ∈ t) (hyt : y ∈ t) : c ∈ t := by
  rw [he] at hn ht
  by_contra hct
  have hd := (List.nodup_append.mp hn).2.2
  rcases infix_avoid_separator ht hct with hL | hR
  · exact hd y (hL.subset hyt) y (by simp [hyR]) rfl
  · exact hd x hxL x (by simp [hR.subset hxt]) rfl

private theorem predecessor {Y : Type*} {a f : Y} {l : List Y} (hf : f ∈ l) :
    ∃ p e s, a :: l = p ++ e :: f :: s := by
  induction l generalizing a with
  | nil => simp at hf
  | cons b l ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨[],a,l,rfl⟩
    · obtain ⟨p,e,s,he⟩ := ih (a := b) hf
      exact ⟨a :: p,e,s,by simpa only [List.cons_append] using congrArg (List.cons a) he⟩

/-- Literally (R\\{alpha,beta}),alpha,beta,q,xi_r,...,xi_1,
(Blue\\{xi_1,...,xi_r}). Residual coordinates are enumerated, not discarded. -/
def cycleWord (Ω Blue : Finset X) (q alpha beta : X) (P : List X) : List X :=
  ((Ω \ insert q Blue) \ {alpha,beta}).toList ++
    alpha :: beta :: q :: (P ++ (Blue \ P.toFinset).toList)

theorem cycleWord_perm {Ω Blue : Finset X} {q alpha beta : X} {P : List X}
    (hq : q ∈ Ω) (hBlue : Blue ⊆ Ω.erase q)
    (hα : alpha ∈ Ω \ insert q Blue) (hβ : beta ∈ Ω \ insert q Blue)
    (hαβ : alpha ≠ beta) (hP : P.Nodup) (hPB : ∀ x ∈ P, x ∈ Blue) :
    (cycleWord Ω Blue q alpha beta P).Nodup ∧
      (cycleWord Ω Blue q alpha beta P).Perm Ω.toList := by
  let U := ((Ω \ insert q Blue) \ {alpha,beta}).toList
  let V := (Blue \ P.toFinset).toList
  let w := cycleWord Ω Blue q alpha beta P
  have hαΩ := (Finset.mem_sdiff.mp hα).1
  have hβΩ := (Finset.mem_sdiff.mp hβ).1
  have hαq : alpha ≠ q := by
    intro he
    exact (Finset.mem_sdiff.mp hα).2 (by simp [he])
  have hβq : beta ≠ q := by
    intro he
    exact (Finset.mem_sdiff.mp hβ).2 (by simp [he])
  have hαB : alpha ∉ Blue := fun hx =>
    (Finset.mem_sdiff.mp hα).2 (Finset.mem_insert_of_mem hx)
  have hβB : beta ∉ Blue := fun hx =>
    (Finset.mem_sdiff.mp hβ).2 (Finset.mem_insert_of_mem hx)
  have hqB : q ∉ Blue := by
    intro hx
    exact (Finset.mem_erase.mp (hBlue hx)).1 rfl
  have hPV (x : X) (hx : x ∈ P ++ V) : x ∈ Blue := by
    rcases List.mem_append.mp hx with hx | hx
    · exact hPB x hx
    · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1
  have hPVnd : (P ++ V).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hP,Finset.nodup_toList _,?_⟩
    intro x hx y hy he
    subst y
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).2
      (List.mem_toFinset.mpr hx)
  have hαPV : alpha ∉ P ++ V := fun hx => hαB (hPV alpha hx)
  have hβPV : beta ∉ P ++ V := fun hx => hβB (hPV beta hx)
  have hqPV : q ∉ P ++ V := fun hx => hqB (hPV q hx)
  have htail : (alpha :: beta :: q :: (P ++ V)).Nodup := by
    simp [List.nodup_cons,hαβ,hαq,hβq,hαPV,hβPV,hqPV,hPVnd]
  have hn : w.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _,htail,?_⟩
    intro x hx y hy he
    subst y
    have hx' := Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)
    rcases List.mem_cons.mp hy with he | hy
    · exact hx'.2 (by simp [he])
    rcases List.mem_cons.mp hy with he | hy
    · exact hx'.2 (by simp [he])
    rcases List.mem_cons.mp hy with he | hy
    · exact (Finset.mem_sdiff.mp hx'.1).2 (by simp [he])
    · exact (Finset.mem_sdiff.mp hx'.1).2 (Finset.mem_insert_of_mem (hPV x hy))
  have hm (x : X) : x ∈ w ↔ x ∈ Ω := by
    change x ∈ U ++ alpha :: beta :: q :: (P ++ V) ↔ x ∈ Ω
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp
          (Finset.mem_toList.mp hx)).1).1
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hαΩ
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hβΩ
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hq
      · exact (Finset.mem_erase.mp (hBlue (hPV x hx))).2
    · intro hxΩ
      by_cases hxα : x = alpha
      · simp [hxα]
      by_cases hxβ : x = beta
      · simp [hxβ]
      by_cases hxq : x = q
      · simp [hxq]
      by_cases hxB : x ∈ Blue
      · by_cases hxP : x ∈ P
        · simp [hxP]
        · have hxV : x ∈ V := by simp [V,hxB,hxP]
          simp [hxV]
      · have hxU : x ∈ U := by simp [U,hxΩ,hxα,hxβ,hxq,hxB]
        simp [hxU]
  exact ⟨hn,(List.perm_ext_iff_of_nodup hn Ω.nodup_toList).mpr
    (fun x => by simpa only [Finset.mem_toList] using hm x)⟩

/-- A conditional ORIGINAL all-C endpoint. Its inputs are geometric cycle data
and an explicit disjoint Boolean decomposition, not atomic interval contradictions.
All q-free unions, larger rows, exterior stars, unused IDs and parallel ports
are handled in this proof. It makes no primitive or fullGood assertion. -/
theorem avoiding_word_of_portCycle (G : Geometry M Ω q)
    {Blue : Finset X} (hBlue : Blue ⊆ Ω.erase q)
    {b0 a z : Finset X} (hb0 : b0 ∈ G.B)
    (ha : a ∈ terminalNeighbors M Ω q b0)
    (hz : z ∈ neighborhood M Ω q) (haz : a ≠ z)
    (C : PortCycle G Blue a)
    {alpha beta : X} (hαa : alpha ∈ a)
    (hαR : alpha ∈ Ω \ insert q Blue) (hβR : beta ∈ Ω \ insert q Blue)
    (hαβ : alpha ≠ beta) (hβN : neighborhood M Ω beta = {z,b0})
    (hmixed : ∀ S ∈ minimalFamily M Ω, q ∉ S →
      (∃ x ∈ S, x ∈ Ω \ insert q Blue) ∧ (∃ y ∈ S, y ∈ Blue))
    (hdecomp : ∀ A, Complete M Ω A →
      ∃ Q : Finset (Finset X), Q ⊆ minimalFamily M Ω ∧ Independent Q ∧
        A = Q.biUnion id) :
    let P := (C.first :: C.tail).map Prod.snd
    let w := cycleWord Ω Blue q alpha beta P
    w.Perm Ω.toList ∧ ∀ t : List X, t <:+: w → ¬Complete M Ω t.toFinset := by
  let P := (C.first :: C.tail).map Prod.snd
  let U := ((Ω \ insert q Blue) \ {alpha,beta}).toList
  let V := (Blue \ P.toFinset).toList
  let w := cycleWord Ω Blue q alpha beta P
  have hPB (x : X) (hx : x ∈ P) : x ∈ Blue := by
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact C.port_blue e he
  obtain ⟨hn,hperm⟩ := cycleWord_perm G.q_mem hBlue hαR hβR hαβ
    (C.ports_nodup G) hPB
  refine ⟨hperm,?_⟩
  intro t htw hCt
  obtain ⟨Q,hQP,hQI,hcover⟩ := hdecomp t.toFinset hCt
  have in_union {S : Finset X} (hSQ : S ∈ Q) {x : X} (hxS : x ∈ S) : x ∈ t := by
    apply List.mem_toFinset.mp
    rw [hcover]
    exact Finset.mem_biUnion.mpr ⟨S,hSQ,hxS⟩
  have union_absent {x : X} (hx : x ∉ Q.biUnion id) : x ∉ t := by
    intro hxt
    exact hx (hcover ▸ List.mem_toFinset.mpr hxt)
  have hleftR (x : X) (hx : x ∈ U ++ [alpha,beta]) : x ∈ Ω \ insert q Blue := by
    rcases List.mem_append.mp hx with hx | hx
    · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hαR
      · have he : x = beta := by simpa using hx
        exact he.symm ▸ hβR
  have hrightB (x : X) (hx : x ∈ P ++ V) : x ∈ Blue := by
    rcases List.mem_append.mp hx with hx | hx
    · exact hPB x hx
    · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1
  by_cases hqt : q ∈ t
  · have hqA : q ∈ Q.biUnion id := hcover ▸ List.mem_toFinset.mpr hqt
    obtain ⟨d,hdQ,hqd⟩ := Finset.mem_biUnion.mp hqA
    have hdT : d ∈ neighborhood M Ω q := mem_neighborhood.mpr ⟨hQP hdQ,hqd⟩
    by_cases hda : d = a
    · have haQ : a ∈ Q := hda ▸ hdQ
      have hαt := in_union haQ hαa
      have hβnot : beta ∉ t := union_absent (forbidden_port G hQP hQI
        haQ (mem_terminalNeighbors.mp ha).1 hz haz.symm hb0 ha hβN)
      have hw : w = (U ++ [alpha]) ++ beta :: (q :: (P ++ V)) := by
        simp [w,cycleWord,U,V,List.append_assoc]
      exact hβnot (infix_crosses hn htw hw (by simp) (by simp) hαt hqt)
    · have hdmap : d ∈ (C.first :: C.tail).map Prod.fst := by
        apply List.mem_toFinset.mp
        rw [C.terminals_cover]
        exact hdT
      obtain ⟨f,hf,hfd⟩ := List.mem_map.mp hdmap
      have hft : f ∈ C.tail := by
        rcases List.mem_cons.mp hf with he | he
        · have hfirst : d = a := hfd.symm.trans
            ((congrArg Prod.fst he).trans C.first_terminal)
          exact (hda hfirst).elim
        · exact he
      obtain ⟨p,e,s,hsplit⟩ := predecessor (a := C.first) hft
      have heL : e ∈ C.first :: C.tail := by rw [hsplit]; simp
      have hpair : [e,f] <:+: C.first :: C.tail := by
        exact ⟨p,s,by simpa [List.append_assoc] using hsplit.symm⟩
      have hstep : PortStep G e f := List.isChain_pair.mp
        (C.steps.left_of_append.infix hpair)
      obtain ⟨b,hb,heN,hfb⟩ := hstep
      have hnd : ((p.map Prod.fst) ++ e.1 :: f.1 :: s.map Prod.fst).Nodup := by
        simpa only [hsplit,List.map_append,List.map_cons] using C.terminals_nodup
      have hnd' := (List.nodup_append.mp hnd).2.1
      have hef : e.1 ≠ f.1 := by
        intro he
        exact (List.nodup_cons.mp hnd').1 (by simp [he])
      have hed : e.1 ≠ d := fun he => hef (he.trans hfd.symm)
      have heAbsent : e.2 ∉ t := union_absent (forbidden_port G hQP hQI hdQ hdT
        (C.terminal_mem G heL) hed hb (hfd ▸ hfb) heN)
      obtain ⟨c,hc,hfN⟩ := C.port_incidence f hf
      have hfmem : f.2 ∈ d := by
        have hmem : f.1 ∈ neighborhood M Ω f.2 := by rw [hfN]; simp
        exact hfd ▸ (mem_neighborhood.mp hmem).2
      have hfPresent := in_union hdQ hfmem
      have hPsplit : P = p.map Prod.snd ++ e.2 :: f.2 :: s.map Prod.snd := by
        change (C.first :: C.tail).map Prod.snd = _
        rw [hsplit]
        simp only [List.map_append,List.map_cons]
      have hw : w = (U ++ [alpha,beta,q] ++ p.map Prod.snd) ++
          e.2 :: (f.2 :: (s.map Prod.snd ++ V)) := by
        change U ++ alpha :: beta :: q :: (P ++ V) = _
        rw [hPsplit]
        simp only [List.append_assoc,List.cons_append,List.nil_append]
      exact heAbsent (infix_crosses hn htw hw (by simp) (by simp) hqt hfPresent)
  · obtain ⟨x,hxA⟩ := hCt.2.1
    have hxU : x ∈ Q.biUnion id := hcover ▸ hxA
    obtain ⟨S,hSQ,hxS⟩ := Finset.mem_biUnion.mp hxU
    have hqS : q ∉ S := fun hqS => hqt (in_union hSQ hqS)
    obtain ⟨⟨r,hrS,hrR⟩,b,hbS,hbB⟩ := hmixed S (hQP hSQ) hqS
    have hrt := in_union hSQ hrS
    have hbt := in_union hSQ hbS
    have hw : w = (U ++ [alpha,beta]) ++ q :: (P ++ V) := by
      simp [w,cycleWord,U,V,List.append_assoc]
    have htw' : t <:+: (U ++ [alpha,beta]) ++ q :: (P ++ V) := hw ▸ htw
    rcases infix_avoid_separator htw' hqt with hL | hR
    · exact (Finset.mem_sdiff.mp (hleftR b (hL.subset hbt))).2
        (Finset.mem_insert_of_mem hbB)
    · exact (Finset.mem_sdiff.mp hrR).2
        (Finset.mem_insert_of_mem (hrightB r (hR.subset hrt)))

/-- Consumed native-colouring consequence. Everything local, including mixed B
stars and the actual red alpha/beta, is constructed above. `houtside` is only
the separate exterior mixed-colouring obligation; it includes private ports
as distinct original IDs. `hdecomp` ranges over ALL Complete rows.

The actual PortCycle is constructed by exists_portCycle, consuming the
Hamilton proof above and both endpoint rank bounds. The earlier positive-
geometry derivation and full original positiveGood are not asserted. Section
5a is a separate formalization obligation. -/
theorem native_avoiding_word (H : Finset (Finset X))
    (G : Geometry (originalSpan H) Ω q) (b0 a z u : Finset X)
    (rank : Finset X → ℕ) (hb0 : b0 ∈ G.B)
    (ha : a ∈ terminalNeighbors (originalSpan H) Ω q b0)
    (hz : z ∈ terminalNeighbors (originalSpan H) Ω q b0) (haz : a ≠ z)
    (hu : u ∈ neighborhood (originalSpan H) Ω q)
    (hu0 : u ∉ terminalNeighbors (originalSpan H) Ω q b0)
    (hrank : ∀ s ∈ neighborhood (originalSpan H) Ω q,
      ∀ t ∈ neighborhood (originalSpan H) Ω q,
      rank s = rank t → s = t)
    (hmin : ∀ t ∈ neighborhood (originalSpan H) Ω q, rank a ≤ rank t)
    (hmax : ∀ t ∈ neighborhood (originalSpan H) Ω q, rank t ≤ rank z)
    {K : Finset X} (hK : K ⊆ Ω.erase q)
    (hKB : ∀ b ∈ G.B, Disjoint K b)
    (houtside : ∀ S ∈ minimalFamily (originalSpan H) Ω, q ∉ S → S ∉ G.B →
      (∃ x ∈ S, x ∈ red G b0 z rank K) ∧
        (∃ y ∈ S, y ∈ blue G b0 z rank K))
    (hdecomp : ∀ A, Complete (originalSpan H) Ω A →
      ∃ Q : Finset (Finset X), Q ⊆ minimalFamily (originalSpan H) Ω ∧ Independent Q ∧
        A = Q.biUnion id) :
    ∃ (C : PortCycle G (blue G b0 z rank K) a) (alpha beta : X),
      alpha ∈ a ∧ alpha ∈ red G b0 z rank K ∧ beta ∈ red G b0 z rank K ∧
      alpha ≠ beta ∧
      let P := (C.first :: C.tail).map Prod.snd
      let w := cycleWord Ω (blue G b0 z rank K) q alpha beta P
      w.Perm Ω.toList ∧ ∀ t : List X, t <:+: w →
        ¬Complete (originalSpan H) Ω t.toFinset := by
  obtain ⟨C⟩ := exists_portCycle G b0 a z u rank hb0 ha hz haz hu hu0
    hrank hmin hmax hKB
  obtain ⟨alpha,beta,hαa,hαR,hβR,hαβ,hβN⟩ :=
    red_frame G b0 a z u rank hb0 ha hz haz hu hu0 hmin hKB
  refine ⟨C,alpha,beta,hαa,hαR,hβR,hαβ,?_⟩
  apply avoiding_word_of_portCycle G (blue_subset G b0 z rank hK) hb0 ha
    (mem_terminalNeighbors.mp hz).1 haz C hαa hαR hβR hαβ hβN
  · intro S hSP hqS
    by_cases hSB : S ∈ G.B
    · exact mixed_B G b0 z rank hz hrank hKB hSB
    · exact houtside S hSP hqS hSB
  · exact hdecomp

/- Section 5a; appended in the canonical PositiveChargePorts namespace.
   Private infix_crosses stays here; the old separator is already public. -/

/-- The literal universal-neighbour word; all residual original IDs remain. -/
def universalWord (Ω Blue : Finset X) (q l rho : X) : List X :=
  ((Ω \ insert q Blue).erase l).toList ++
    l :: q :: rho :: (Blue.erase rho).toList

/-- Both residual sides may be empty. This is a literal all-Ω permutation. -/
theorem universalWord_perm {Blue : Finset X} {l rho : X}
    (hq : q ∈ Ω) (hBlue : Blue ⊆ Ω.erase q)
    (hl : l ∈ Ω \ insert q Blue) (hrho : rho ∈ Blue) :
    (universalWord Ω Blue q l rho).Nodup ∧
      (universalWord Ω Blue q l rho).Perm Ω.toList := by
  let R := Ω \ insert q Blue
  let U := (R.erase l).toList
  let V := (Blue.erase rho).toList
  let w := universalWord Ω Blue q l rho
  have hlΩ := (Finset.mem_sdiff.mp hl).1
  have hlq : l ≠ q := by
    intro he
    exact (Finset.mem_sdiff.mp hl).2 (by simp [he])
  have hlB : l ∉ Blue := fun hx =>
    (Finset.mem_sdiff.mp hl).2 (Finset.mem_insert_of_mem hx)
  have hqB : q ∉ Blue := fun hx => (Finset.mem_erase.mp (hBlue hx)).1 rfl
  have hrhoq : rho ≠ q := (Finset.mem_erase.mp (hBlue hrho)).1
  have hlrho : l ≠ rho := fun he => hlB (he.symm ▸ hrho)
  have hVB {x : X} (hx : x ∈ V) : x ∈ Blue :=
    Finset.mem_of_mem_erase (Finset.mem_toList.mp hx)
  have hlV : l ∉ V := fun hx => hlB (hVB hx)
  have hqV : q ∉ V := fun hx => hqB (hVB hx)
  have hrhoV : rho ∉ V := by simp [V]
  have hVN : V.Nodup := Finset.nodup_toList _
  have htail : (l :: q :: rho :: V).Nodup := by
    simp [List.nodup_cons,hlq,hlrho,hrhoq.symm,hlV,hqV,hrhoV,
      hVN]
  have hn : w.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _,htail,?_⟩
    intro x hx y hy he
    subst y
    have hxE := Finset.mem_erase.mp (Finset.mem_toList.mp hx)
    have hxR := Finset.mem_sdiff.mp hxE.2
    rcases List.mem_cons.mp hy with he | hy
    · exact hxE.1 he
    rcases List.mem_cons.mp hy with he | hy
    · exact hxR.2 (by simp [he])
    rcases List.mem_cons.mp hy with he | hy
    · exact hxR.2 (Finset.mem_insert_of_mem (he.symm ▸ hrho))
    · exact hxR.2 (Finset.mem_insert_of_mem (hVB hy))
  have hm (x : X) : x ∈ w ↔ x ∈ Ω := by
    change x ∈ U ++ l :: q :: rho :: V ↔ x ∈ Ω
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (Finset.mem_sdiff.mp (Finset.mem_erase.mp
          (Finset.mem_toList.mp hx)).2).1
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hlΩ
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hq
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (Finset.mem_erase.mp (hBlue hrho)).2
      · exact (Finset.mem_erase.mp (hBlue (hVB hx))).2
    · intro hxΩ
      by_cases hxl : x = l
      · simp [hxl]
      by_cases hxq : x = q
      · simp [hxq]
      by_cases hxr : x = rho
      · simp [hxr]
      by_cases hxB : x ∈ Blue
      · have hxV : x ∈ V := by simp [V,hxB,hxr]
        simp [hxV]
      · have hxU : x ∈ U := by simp [U,R,hxΩ,hxl,hxq,hxB]
        simp [hxU]
  exact ⟨hn,(List.perm_ext_iff_of_nodup hn Ω.nodup_toList).mpr
    (fun x => by simpa only [Finset.mem_toList] using hm x)⟩

/-- Section 5a's all-Complete-row interval proof. The exact two original
suppliers of l and rho exclude extra selected rows, including exterior rows.
The red witness at v and a blue witness at EVERY terminal are constructed
by the RawBlock consumer, rather than assumed at the final target. -/
theorem universal_avoiding_word {Blue : Finset X} {b0 u v : Finset X}
    {l rho b : X}
    (hq : q ∈ Ω) (hBlue : Blue ⊆ Ω.erase q)
    (hlR : l ∈ Ω \ insert q Blue) (hrhoB : rho ∈ Blue)
    (hu : u ∈ neighborhood M Ω q) (hv : v ∈ neighborhood M Ω q) (huv : u ≠ v)
    (hb0q : q ∉ b0)
    (huni : ∀ d ∈ neighborhood M Ω q, d ∈ terminalNeighbors M Ω q b0)
    (hlN : neighborhood M Ω l = {u,b0})
    (hrhoN : neighborhood M Ω rho = {v,b0})
    (hbv : b ∈ v) (hbR : b ∈ Ω \ insert q Blue)
    (hterminal : ∀ d ∈ neighborhood M Ω q, ∃ x ∈ d, x ∈ Blue)
    (hmixed : ∀ S ∈ minimalFamily M Ω, q ∉ S →
      (∃ x ∈ S, x ∈ Ω \ insert q Blue) ∧ (∃ y ∈ S, y ∈ Blue))
    (hdecomp : ∀ A, Complete M Ω A →
      ∃ Q : Finset (Finset X), Q ⊆ minimalFamily M Ω ∧ Independent Q ∧
        A = Q.biUnion id) :
    (universalWord Ω Blue q l rho).Perm Ω.toList ∧
      ∀ f : List X, f <:+: universalWord Ω Blue q l rho →
        ¬Complete M Ω f.toFinset := by
  let R := Ω \ insert q Blue
  let U := (R.erase l).toList
  let V := (Blue.erase rho).toList
  let w := universalWord Ω Blue q l rho
  obtain ⟨hn,hperm⟩ := universalWord_perm hq hBlue hlR hrhoB
  refine ⟨hperm,?_⟩
  intro f hfw hCf
  obtain ⟨Q,hQP,hQI,hcover⟩ := hdecomp f.toFinset hCf
  have in_union {S : Finset X} (hS : S ∈ Q) {x : X} (hx : x ∈ S) : x ∈ f := by
    apply List.mem_toFinset.mp
    rw [hcover]
    exact Finset.mem_biUnion.mpr ⟨S,hS,hx⟩
  have forbidden {s d : Finset X} {x : X} (hdQ : d ∈ Q)
      (hdT : d ∈ neighborhood M Ω q) (hsT : s ∈ neighborhood M Ω q)
      (hsd : s ≠ d) (hxN : neighborhood M Ω x = {s,b0}) : x ∉ f := by
    intro hxf
    have hxU : x ∈ Q.biUnion id := hcover ▸ List.mem_toFinset.mpr hxf
    obtain ⟨D,hDQ,hxD⟩ := Finset.mem_biUnion.mp hxU
    have hDN : D ∈ ({s,b0} : Finset (Finset X)) := by
      rw [← hxN]
      exact mem_neighborhood.mpr ⟨hQP hDQ,hxD⟩
    rcases Finset.mem_insert.mp hDN with hDs | hDb
    · subst D
      exact hsd (selected_terminal_unique hQI hDQ hdQ hsT hdT)
    · have hDb' : D = b0 := Finset.mem_singleton.mp hDb
      subst D
      obtain ⟨y,hy⟩ := (mem_terminalNeighbors.mp (huni d hdT)).2
      have hy' := Finset.mem_inter.mp hy
      have he := selected_unique hQI hDQ hdQ hy'.1 hy'.2
      exact hb0q (he.symm ▸ (mem_neighborhood.mp hdT).2)
  have hleft {x : X} (hx : x ∈ U ++ [l]) : x ∈ R := by
    rcases List.mem_append.mp hx with hx | hx
    · exact Finset.mem_of_mem_erase (Finset.mem_toList.mp hx)
    · have he : x = l := by simpa using hx
      exact he.symm ▸ hlR
  have hright {x : X} (hx : x ∈ rho :: V) : x ∈ Blue := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hrhoB
    · exact Finset.mem_of_mem_erase (Finset.mem_toList.mp hx)
  by_cases hqf : q ∈ f
  · have hqU : q ∈ Q.biUnion id := hcover ▸ List.mem_toFinset.mpr hqf
    obtain ⟨d,hdQ,hqd⟩ := Finset.mem_biUnion.mp hqU
    have hdT : d ∈ neighborhood M Ω q := mem_neighborhood.mpr ⟨hQP hdQ,hqd⟩
    by_cases hdv : d = v
    · have hvQ : v ∈ Q := hdv ▸ hdQ
      have hbf := in_union hvQ hbv
      have hlnot := forbidden hvQ hv hu huv hlN
      have hlf : l ∈ f := by
        by_cases hbl : b = l
        · exact hbl ▸ hbf
        · have hbU : b ∈ U := by simp [U,R,hbR,hbl]
          have hw : w = U ++ l :: (q :: rho :: V) := rfl
          exact infix_crosses hn hfw hw hbU (by simp) hbf hqf
      exact hlnot hlf
    · obtain ⟨x,hxd,hxB⟩ := hterminal d hdT
      have hxf := in_union hdQ hxd
      have hrhonot := forbidden hdQ hdT hv (Ne.symm hdv) hrhoN
      have hrhof : rho ∈ f := by
        by_cases hxr : x = rho
        · exact hxr ▸ hxf
        · have hxV : x ∈ V := by simp [V,hxB,hxr]
          have hw : w = (U ++ [l,q]) ++ rho :: V := by
            simp [w,universalWord,U,R,V,List.append_assoc]
          exact infix_crosses hn hfw hw (by simp) hxV hqf hxf
      exact hrhonot hrhof
  · obtain ⟨x,hxf⟩ := hCf.2.1
    have hxU : x ∈ Q.biUnion id := hcover ▸ hxf
    obtain ⟨S,hSQ,hxS⟩ := Finset.mem_biUnion.mp hxU
    have hqS : q ∉ S := fun hqS => hqf (in_union hSQ hqS)
    obtain ⟨⟨r,hrS,hrR⟩,y,hyS,hyB⟩ := hmixed S (hQP hSQ) hqS
    have hrf := in_union hSQ hrS
    have hyf := in_union hSQ hyS
    have hw : w = (U ++ [l]) ++ q :: (rho :: V) := by
      simp [w,universalWord,U,R,V,List.append_assoc]
    have hfw' : f <:+: (U ++ [l]) ++ q :: (rho :: V) := hw ▸ hfw
    rcases infix_avoid_separator hfw' hqf with hL | hR
    · exact (Finset.mem_sdiff.mp (hleft (hL.subset hyf))).2
        (Finset.mem_insert_of_mem hyB)
    · exact (Finset.mem_sdiff.mp hrR).2
        (Finset.mem_insert_of_mem (hright (hR.subset hrf)))

end D5.S3.Combinatorics.Sequenceability.PositiveChargePorts
