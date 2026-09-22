/- GID: D5/S3/Factorization/Combinatorics/LoopyEvaluator
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/LoopyEvaluator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The concrete Loopy evaluator obeys its source representation and recursion laws. -/
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Basic
set_option autoImplicit false
namespace D5.S3.Factorization.Combinatorics.LoopyDegreeSequence
noncomputable section
open scoped BigOperators
abbrev Edge := Nat × Nat
abbrev LoopyPolynomial := MvPolynomial Nat (Polynomial Int)
/-- An encoding has all pending edge endpoints in its explicitly retained vertex set,
and stores no accumulated loops away from that set. -/
def Valid (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) : Prop :=
  (∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) ∧ ∀ v, v ∉ V → ell v = 0
/-- Replace the second endpoint of a contracted nonloop by the first. -/
def contractVertex (a b v : Nat) : Nat := if v = b then a else v
/-- Relabel one pending edge after a contraction. -/
def contractEdge (a b : Nat) (e : Edge) : Edge :=
  (contractVertex a b e.1, contractVertex a b e.2)
/-- Move one pending loop into the loop accumulator. -/
def addLoop (ell : Nat → Nat) (a : Nat) : Nat → Nat :=
  Function.update ell a (ell a + 1)
/-- Retain a contracted edge as a loop, merge the endpoint loop counts, and erase
the discarded representative's accumulator entry. -/
def contractLoops (ell : Nat → Nat) (a b : Nat) : Nat → Nat := fun v =>
  if v = a then ell a + ell b + 1 else if v = b then 0 else ell v
/-- Relabel a pending edge by a permutation of the ambient labels. -/
def relabelEdge (f : Equiv.Perm Nat) (e : Edge) : Edge := (f e.1, f e.2)
/-- Transport the loop accumulator along a permutation of the ambient labels. -/
def relabelLoops (f : Equiv.Perm Nat) (ell : Nat → Nat) : Nat → Nat := fun v =>
  ell (f.symm v)
/-- Combine loop accumulators on disjoint vertex sets. -/
def unionLoops (ell₁ ell₂ : Nat → Nat) : Nat → Nat := fun v => ell₁ v + ell₂ v
/-- The source recursion on raw undirected pending endpoint pairs. Every call
consumes exactly one list occurrence. A nonloop contraction retains that occurrence
as one accumulated loop. -/
def loopyAux : Finset Nat → List Edge → (Nat → Nat) → LoopyPolynomial
  | V, [], ell => ∏ v ∈ V, MvPolynomial.X (ell v)
  | V, (a, b) :: E, ell =>
      if a = b then
        loopyAux V E (addLoop ell a)
      else
        loopyAux (V.erase b) (E.map (contractEdge a b)) (contractLoops ell a b) +
          MvPolynomial.C Polynomial.X * loopyAux V E ell
termination_by V E ell => E.length
decreasing_by all_goals simp_wf
/-- Concrete ordinary Loopy evaluator. -/
def loopy (V : Finset Nat) (E : List Edge) (ell : Nat → Nat := fun _ => 0) :
    LoopyPolynomial :=
  loopyAux V E ell
/-- The concrete recursion is independent of its finite labelled representation and
obeys the source operations, including disjoint-union multiplication
(Definition 1.1 and Proposition 2.1 of arXiv:2609.07728v1). -/
theorem loopy_spec :
    (∀ (f : Equiv.Perm Nat) (V : Finset Nat) (E : List Edge) (ell : Nat → Nat),
        loopy (V.map f.toEmbedding) (E.map (relabelEdge f)) (relabelLoops f ell) =
          loopy V E ell) ∧
      (∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) (a b : Nat),
        Valid V ((a, b) :: E) ell →
          loopy V ((a, b) :: E) ell = loopy V ((b, a) :: E) ell) ∧
      (∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) (e f : Edge),
        Valid V (e :: f :: E) ell →
          loopy V (e :: f :: E) ell = loopy V (f :: e :: E) ell) ∧
      (∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) (a : Nat),
        loopy V ((a, a) :: E) ell = loopy V E (addLoop ell a)) ∧
      (∀ (V : Finset Nat) (E E' : List Edge) (ell : Nat → Nat),
        E.Perm E' → Valid V E ell → loopy V E ell = loopy V E' ell) ∧
      (∀ (V : Finset Nat) (E R : List Edge) (ell : Nat → Nat) (e : Edge),
        E.Perm (e :: R) → Valid V E ell →
          loopy V E ell =
            if e.1 = e.2 then loopy V R (addLoop ell e.1)
            else loopy (V.erase e.2) (R.map (contractEdge e.1 e.2))
              (contractLoops ell e.1 e.2) +
              MvPolynomial.C Polynomial.X * loopy V R ell) ∧
      (∀ (V₁ V₂ : Finset Nat) (E₁ E₂ : List Edge) (ell₁ ell₂ : Nat → Nat),
        Disjoint V₁ V₂ → Valid V₁ E₁ ell₁ → Valid V₂ E₂ ell₂ →
          loopyAux (V₁ ∪ V₂) (E₁ ++ E₂) (unionLoops ell₁ ell₂) =
            loopyAux V₁ E₁ ell₁ * loopyAux V₂ E₂ ell₂) := by
  classical
  have relabelCore : ∀ n : Nat, ∀ (f : Equiv.Perm Nat) (V : Finset Nat)
      (E : List Edge) (ell : Nat → Nat), E.length = n →
      loopyAux (V.map f.toEmbedding) (E.map (relabelEdge f)) (relabelLoops f ell) =
        loopyAux V E ell := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro f V E ell hlen
        cases E with
        | nil =>
            simp only [List.map_nil, loopyAux]
            rw [Finset.prod_map]
            apply Finset.prod_congr rfl
            intro v hv
            simp [relabelLoops]
        | cons e E =>
            rcases e with ⟨a, b⟩
            have hlt : E.length < n := by
              have hsucc : E.length + 1 = n := by simpa using hlen
              omega
            by_cases hab : a = b
            · subst b
              have hloops :
                  relabelLoops f (addLoop ell a) =
                    addLoop (relabelLoops f ell) (f a) := by
                funext v
                by_cases hv : v = f a
                · subst v
                  simp [relabelLoops, addLoop]
                · have hpre : f.symm v ≠ a := by
                    intro heq
                    apply hv
                    simpa using congrArg f heq
                  simp [relabelLoops, addLoop, hv, hpre]
              simp only [List.map_cons, relabelEdge, loopyAux, Equiv.apply_eq_iff_eq]
              rw [← hloops]
              exact ih E.length hlt f V E (addLoop ell a) rfl
            · have hfab : f a ≠ f b := f.injective.ne hab
              have hvertices :
                  (V.map f.toEmbedding).erase (f b) = (V.erase b).map f.toEmbedding := by
                ext v
                simp
              have hedges :
                  (E.map (relabelEdge f)).map (contractEdge (f a) (f b)) =
                    (E.map (contractEdge a b)).map (relabelEdge f) := by
                rw [List.map_map, List.map_map]
                apply List.map_congr_left
                intro e he
                rcases e with ⟨x, y⟩
                simp only [Function.comp_apply, relabelEdge, contractEdge, Prod.fst,
                  Prod.snd]
                apply Prod.ext
                · by_cases hx : x = b <;> simp [contractVertex, hx]
                · by_cases hy : y = b <;> simp [contractVertex, hy]
              have hloops :
                  contractLoops (relabelLoops f ell) (f a) (f b) =
                    relabelLoops f (contractLoops ell a b) := by
                funext v
                by_cases hva : v = f a
                · subst v
                  simp [contractLoops, relabelLoops, hab]
                · by_cases hvb : v = f b
                  · subst v
                    simp [contractLoops, relabelLoops, hfab, hab, Ne.symm hab]
                  · have hpa : f.symm v ≠ a := by
                      intro heq
                      apply hva
                      simpa using congrArg f heq
                    have hpb : f.symm v ≠ b := by
                      intro heq
                      apply hvb
                      simpa using congrArg f heq
                    simp [contractLoops, relabelLoops, hva, hvb, hpa, hpb]
              simp only [List.map_cons, relabelEdge, loopyAux, hfab, hab, if_false]
              rw [hvertices, hedges, hloops]
              rw [ih (E.map (contractEdge a b)).length (by simpa using hlt) f
                (V.erase b) (E.map (contractEdge a b)) (contractLoops ell a b) rfl]
              rw [ih E.length hlt f V E ell rfl]
  have hrelabel (f : Equiv.Perm Nat) (V : Finset Nat) (E : List Edge)
      (ell : Nat → Nat) :
      loopy (V.map f.toEmbedding) (E.map (relabelEdge f)) (relabelLoops f ell) =
        loopy V E ell := by
    rw [loopy, loopy]
    exact relabelCore E.length f V E ell rfl
  have haddComm (ell : Nat → Nat) (a b : Nat) :
      addLoop (addLoop ell a) b = addLoop (addLoop ell b) a := by
    funext v
    by_cases hab : a = b
    · subst b
      simp [addLoop]
    · by_cases hva : v = a <;> by_cases hvb : v = b <;>
        simp_all [addLoop, Nat.add_comm, Nat.add_left_comm]
  have hloopContract (ell : Nat → Nat) (a c d : Nat) (hcd : c ≠ d) :
      contractLoops (addLoop ell a) c d =
        addLoop (contractLoops ell c d) (contractVertex c d a) := by
    funext v
    by_cases hac : a = c
    · subst a
      by_cases hvc : v = c <;> by_cases hvd : v = d <;>
        simp_all [addLoop, contractLoops, contractVertex, Ne.symm hcd] <;> omega
    · by_cases had : a = d
      · subst a
        by_cases hvc : v = c <;> by_cases hvd : v = d <;>
          simp_all [addLoop, contractLoops, contractVertex, Ne.symm hcd] <;> omega
      · by_cases hvc : v = c <;> by_cases hvd : v = d <;> by_cases hva : v = a <;>
          simp_all [addLoop, contractLoops, contractVertex, Ne.symm hac, Ne.symm had]
  have hdouble (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) (a b c d : Nat)
      (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V) (hdV : d ∈ V)
      (hab : a ≠ b) (hcd : c ≠ d)
      (hnonparallel : contractVertex a b c ≠ contractVertex a b d) :
      loopyAux ((V.erase b).erase (contractVertex a b d))
          ((E.map (contractEdge a b)).map
            (contractEdge (contractVertex a b c) (contractVertex a b d)))
          (contractLoops (contractLoops ell a b) (contractVertex a b c)
            (contractVertex a b d)) =
        loopyAux ((V.erase d).erase (contractVertex c d b))
          ((E.map (contractEdge c d)).map
            (contractEdge (contractVertex c d a) (contractVertex c d b)))
          (contractLoops (contractLoops ell c d) (contractVertex c d a)
            (contractVertex c d b)) := by
    by_cases hdb : d = b
    · subst d
      have hca : c ≠ a := by
        intro h
        subst c
        exact hnonparallel (by simp [contractVertex])
      have hcb : c ≠ b := by
        intro h
        subst c
        exact hcd rfl
      have hba : b ≠ a := Ne.symm hab
      have hbc : b ≠ c := Ne.symm hcb
      let f : Equiv.Perm Nat := Equiv.swap c a
      have hfb : f b = b := by
        exact Equiv.swap_apply_of_ne_of_ne hbc hba
      have hfWhole : V.map f.toEmbedding = V := by
        ext v
        by_cases hvc : v = c
        · subst v
          simp [f, hca, haV, hcV]
        · by_cases hva : v = a
          · subst v
            simp [f, hca, haV, hcV]
          · simp [f, hvc, hva, Equiv.swap_apply_of_ne_of_ne]
      have hfV : ((V.erase b).erase a).map f.toEmbedding = (V.erase b).erase c := by
        rw [Finset.map_erase, Finset.map_erase, hfWhole]
        change (V.erase (f b)).erase (f a) = _
        rw [hfb]
        simp [f]
      have hfE :
          (((E.map (contractEdge a b)).map (contractEdge c a)).map
              (relabelEdge f)) =
            (E.map (contractEdge c b)).map (contractEdge a c) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro e he
        rcases e with ⟨x, y⟩
        apply Prod.ext
        · by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
            simp_all [Function.comp_apply, relabelEdge, contractEdge, contractVertex, f,
              Equiv.swap_apply_def]
        · by_cases hya : y = a <;> by_cases hyb : y = b <;> by_cases hyc : y = c <;>
            simp_all [Function.comp_apply, relabelEdge, contractEdge, contractVertex, f,
              Equiv.swap_apply_def]
      have hfLoops :
          relabelLoops f (contractLoops (contractLoops ell a b) c a) =
            contractLoops (contractLoops ell c b) a c := by
        funext v
        by_cases hva : v = a <;> by_cases hvb : v = b <;> by_cases hvc : v = c <;>
          simp_all [relabelLoops, contractLoops, f, Equiv.swap_apply_def] <;> omega
      have h := relabelCore ((E.map (contractEdge a b)).map (contractEdge c a)).length
        f ((V.erase b).erase a)
        ((E.map (contractEdge a b)).map (contractEdge c a))
        (contractLoops (contractLoops ell a b) c a) rfl
      rw [hfV, hfE, hfLoops] at h
      change loopyAux ((V.erase b).erase c)
          ((E.map (contractEdge c b)).map (contractEdge a c))
          (contractLoops (contractLoops ell c b) a c) =
        loopyAux ((V.erase b).erase a)
          ((E.map (contractEdge a b)).map (contractEdge c a))
          (contractLoops (contractLoops ell a b) c a) at h
      simpa [contractVertex, hcb, hca, hab, hcd] using h.symm
    · have hnotrev : ¬(c = b ∧ d = a) := by
        rintro ⟨rfl, rfl⟩
        exact hnonparallel (by simp [contractVertex])
      have hbd : b ≠ d := Ne.symm hdb
      have hV :
          (V.erase b).erase (contractVertex a b d) =
            (V.erase d).erase (contractVertex c d b) := by
        simp [contractVertex, hdb, Ne.symm hdb, Finset.erase_right_comm]
      have hmap (x : Nat) :
          contractVertex (contractVertex a b c) (contractVertex a b d)
              (contractVertex a b x) =
            contractVertex (contractVertex c d a) (contractVertex c d b)
              (contractVertex c d x) := by
        by_cases hxb : x = b
        · subst x
          by_cases had : a = d <;> by_cases hcb : c = b <;>
            simp_all [contractVertex, hbd]
        · by_cases hxd : x = d
          · subst x
            by_cases had : a = d <;> by_cases hcb : c = b <;>
              simp_all [contractVertex, hbd]
          · simp [contractVertex, hxb, hxd, hdb, hbd]
      have hE :
          (E.map (contractEdge a b)).map
              (contractEdge (contractVertex a b c) (contractVertex a b d)) =
            (E.map (contractEdge c d)).map
              (contractEdge (contractVertex c d a) (contractVertex c d b)) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro e he
        rcases e with ⟨x, y⟩
        apply Prod.ext
        · exact hmap x
        · exact hmap y
      have hLoops :
          contractLoops (contractLoops ell a b) (contractVertex a b c)
              (contractVertex a b d) =
            contractLoops (contractLoops ell c d) (contractVertex c d a)
              (contractVertex c d b) := by
        by_cases had : a = d
        · have hcb : c ≠ b := fun h => hnotrev ⟨h, had.symm⟩
          subst d
          funext v
          by_cases hva : v = a <;> by_cases hvb : v = b <;> by_cases hvc : v = c <;>
            simp_all [contractLoops, contractVertex, Ne.symm hab, Ne.symm hcd,
              Ne.symm hcb] <;> omega
        · by_cases hcb : c = b
          · subst c
            funext v
            by_cases hva : v = a <;> by_cases hvb : v = b <;> by_cases hvd : v = d <;>
              simp_all [contractLoops, contractVertex, hbd, Ne.symm hab, Ne.symm hcd,
                Ne.symm had] <;> omega
          · funext v
            by_cases hva : v = a <;> by_cases hvb : v = b <;>
              by_cases hvc : v = c <;> by_cases hvd : v = d <;>
                simp_all [contractLoops, contractVertex, hbd, Ne.symm hab, Ne.symm hcd,
                  Ne.symm had, Ne.symm hcb] <;> omega
      rw [hV, hE, hLoops]
  have horient : ∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) (a b : Nat),
      Valid V ((a, b) :: E) ell →
        loopy V ((a, b) :: E) ell = loopy V ((b, a) :: E) ell := by
    intro V E ell a b hvalid
    rw [loopy, loopy]
    by_cases hab : a = b
    · subst b
      rfl
    · have haV := (hvalid.1 (a, b) (by simp)).1
      have hbV := (hvalid.1 (a, b) (by simp)).2
      let f : Equiv.Perm Nat := Equiv.swap a b
      have hfV : (V.erase b).map f.toEmbedding = V.erase a := by
        ext v
        by_cases hva : v = a
        · subst v
          simp [f, Equiv.swap_apply_def, hab, Ne.symm hab]
        · by_cases hvb : v = b
          · subst v
            simp [f, Equiv.swap_apply_def, hab, Ne.symm hab, haV, hbV]
          · simp [f, Equiv.swap_apply_def, hab, hva, hvb]
      have hfE : (E.map (contractEdge a b)).map (relabelEdge f) =
          E.map (contractEdge b a) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro e he
        rcases e with ⟨x, y⟩
        apply Prod.ext
        · by_cases hxa : x = a <;> by_cases hxb : x = b <;>
            simp [relabelEdge, contractEdge, contractVertex, f, Equiv.swap_apply_def, *]
        · by_cases hya : y = a <;> by_cases hyb : y = b <;>
            simp [relabelEdge, contractEdge, contractVertex, f, Equiv.swap_apply_def, *]
      have hfLoops : relabelLoops f (contractLoops ell a b) =
          contractLoops ell b a := by
        funext v
        by_cases hva : v = a
        · subst v
          simp [relabelLoops, contractLoops, f, Equiv.swap_apply_def, hab,
            Ne.symm hab, Nat.add_comm]
        · by_cases hvb : v = b
          · subst v
            simp [relabelLoops, contractLoops, f, Equiv.swap_apply_def, hab,
              Ne.symm hab, Nat.add_comm]
          · simp [relabelLoops, contractLoops, f, Equiv.swap_apply_def, hva, hvb]
      simp only [loopyAux, hab, Ne.symm hab, if_false]
      have hcontract := hrelabel f (V.erase b) (E.map (contractEdge a b))
        (contractLoops ell a b)
      rw [hfV, hfE, hfLoops] at hcontract
      change loopyAux (V.erase a) (E.map (contractEdge b a)) (contractLoops ell b a) =
        loopyAux (V.erase b) (E.map (contractEdge a b)) (contractLoops ell a b) at hcontract
      rw [hcontract]
  have hswap : ∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) (e f : Edge),
      Valid V (e :: f :: E) ell →
        loopy V (e :: f :: E) ell = loopy V (f :: e :: E) ell := by
    intro V E ell e f hvalid
    rcases e with ⟨a, b⟩
    rcases f with ⟨c, d⟩
    rw [loopy, loopy]
    by_cases hab : a = b
    ·
      subst b
      by_cases hcd : c = d
      · subst d
        simp only [loopyAux, ↓reduceIte]
        rw [haddComm]
      · simp only [loopyAux, ↓reduceIte, hcd, if_false, List.map_cons, contractEdge,
          Prod.fst, Prod.snd]
        rw [hloopContract ell a c d hcd]
    · by_cases hcd : c = d
      ·
        subst d
        simp only [loopyAux, ↓reduceIte, hab, if_false, List.map_cons, contractEdge,
            Prod.fst, Prod.snd]
        rw [hloopContract ell c a b hab]
      ·
        have haV := (hvalid.1 (a, b) (by simp)).1
        have hbV := (hvalid.1 (a, b) (by simp)).2
        have hcV := (hvalid.1 (c, d) (by simp)).1
        have hdV := (hvalid.1 (c, d) (by simp)).2
        by_cases hparallel :
            contractVertex a b c = contractVertex a b d
        · have hpairs : (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
            by_cases hcb : c = b
            · subst c
              have hda : d = a := by
                have had : a = d := by
                  simpa [contractVertex, Ne.symm hcd] using hparallel
                exact had.symm
              exact Or.inr ⟨rfl, hda⟩
            · by_cases hdb : d = b
              · subst d
                have hca : c = a := by
                  simpa [contractVertex, hcb, hab] using hparallel
                exact Or.inl ⟨hca, rfl⟩
              · exfalso
                have hcd' : c = d := by
                  simpa [contractVertex, hcb, hdb] using hparallel
                exact hcd hcd'
          rcases hpairs with hsame | hreverse
          · rcases hsame with ⟨hca, hdb⟩
            subst c
            subst d
            rfl
          · rcases hreverse with ⟨hcb, hda⟩
            subst c
            subst d
            have htail : Valid V ((a, b) :: E) ell := by
              refine ⟨?_, hvalid.2⟩
              intro e he
              apply hvalid.1 e
              have he' : e = (a, b) ∨ e ∈ E := List.mem_cons.mp he
              exact he'.elim (fun h => List.mem_cons.mpr (Or.inl h))
                (fun h => List.mem_cons.mpr (Or.inr
                  (List.mem_cons.mpr (Or.inr h))))
            have hadded : Valid V ((a, b) :: E) (addLoop ell a) := by
              refine ⟨htail.1, ?_⟩
              intro v hv
              have hva : v ≠ a := fun h => hv (h ▸ haV)
              simp [addLoop, hva, hvalid.2 v hv]
            have hone := horient V E ell a b htail
            rw [loopy, loopy] at hone
            simp only [loopyAux, hab, Ne.symm hab, if_false] at hone
            have hone' :
                loopyAux (V.erase b) (E.map (contractEdge a b))
                    (contractLoops ell a b) =
                  loopyAux (V.erase a) (E.map (contractEdge b a))
                    (contractLoops ell b a) := by
              exact add_right_cancel hone
            have htwo := horient V E (addLoop ell a) a b hadded
            rw [loopy, loopy] at htwo
            simp only [loopyAux, hab, Ne.symm hab, if_false] at htwo
            have htwo' :
                loopyAux (V.erase b) (E.map (contractEdge a b))
                    (addLoop (contractLoops ell a b) a) =
                  loopyAux (V.erase a) (E.map (contractEdge b a))
                    (addLoop (contractLoops ell b a) b) := by
              have hleft :
                  contractLoops (addLoop ell a) a b =
                    addLoop (contractLoops ell a b) a := by
                simpa [contractVertex, hab] using hloopContract ell a a b hab
              have hright :
                  contractLoops (addLoop ell a) b a =
                    addLoop (contractLoops ell b a) b := by
                simpa [contractVertex, Ne.symm hab] using
                  hloopContract ell a b a (Ne.symm hab)
              rw [← hleft, ← hright]
              simpa [contractVertex, hab, Ne.symm hab] using add_right_cancel htwo
            simp [loopyAux, hab, Ne.symm hab, contractEdge, contractVertex]
            rw [htwo', hone']
        · have hparallel' :
            contractVertex c d a ≠ contractVertex c d b := by
            intro hreverse
            by_cases had : a = d
            · subst a
              by_cases hbc : b = c
              · subst b
                exact hparallel (by simp [contractVertex, hcd, hab])
              · have hcb : c = b := by
                  simpa [contractVertex, hbc, Ne.symm hab] using hreverse
                exact hbc hcb.symm
            · by_cases hbd : b = d
              · subst b
                have hca : a = c := by
                  simpa [contractVertex, had, hcd] using hreverse
                exact hparallel (by simp [contractVertex, hca, had, hcd])
              · have hab' : a = b := by
                  simpa [contractVertex, had, hbd] using hreverse
                exact hab hab'
          simp only [loopyAux, hab, hcd, if_false, List.map_cons,
            contractEdge, Prod.fst, Prod.snd, hparallel, hparallel']
          rw [hdouble V E ell a b c d haV hbV hcV hdV hab hcd hparallel]
          ring
  have hloop : ∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat) (a : Nat),
      loopy V ((a, a) :: E) ell = loopy V E (addLoop ell a) := by
    intro V E ell a
    simp [loopy, loopyAux]
  have hcontractValid : ∀ (V : Finset Nat) (E : List Edge) (ell : Nat → Nat)
      (a b : Nat), Valid V ((a, b) :: E) ell → a ≠ b →
        Valid (V.erase b) (E.map (contractEdge a b)) (contractLoops ell a b) := by
    intro V E ell a b hvalid hab
    have haV := (hvalid.1 (a, b) (by simp)).1
    refine ⟨?_, ?_⟩
    · intro e he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      have hfV := hvalid.1 f (by simp [hf])
      have map_mem (x : Nat) (hx : x ∈ V) : contractVertex a b x ∈ V.erase b := by
        by_cases hxb : x = b
        · subst x
          simp [contractVertex, haV, hab]
        · simp [contractVertex, hxb, hx]
      exact ⟨map_mem f.1 hfV.1, map_mem f.2 hfV.2⟩
    · intro v hv
      have hva : v ≠ a := by
        intro h
        subst v
        exact hv (by simp [haV, hab])
      by_cases hvb : v = b
      · subst v
        simp [contractLoops, hva]
      · have hvV : v ∉ V := by
          intro h
          exact hv (by simp [h, hvb])
        simp [contractLoops, hva, hvb, hvalid.2 v hvV]
  have hvalidPerm : ∀ (V : Finset Nat) (E E' : List Edge) (ell : Nat → Nat),
      E.Perm E' → Valid V E ell → Valid V E' ell := by
    intro V E E' ell hp hv
    exact ⟨fun e he => hv.1 e ((hp.mem_iff).2 he), hv.2⟩
  have hpermMap : ∀ (E E' : List Edge), E.Perm E' →
      ∀ (g : Edge → Edge) (V : Finset Nat) (ell : Nat → Nat),
        Valid V (E.map g) ell →
          loopyAux V (E.map g) ell = loopyAux V (E'.map g) ell := by
    intro E E' hp
    induction hp with
    | nil =>
        intro g V ell hv
        rfl
    | @cons x l₁ l₂ hp ih =>
        intro g V ell hv
        simp only [List.map_cons] at hv ⊢
        generalize hx : g x = q at hv ⊢
        rcases q with ⟨a, b⟩
        have htail : Valid V (l₁.map g) ell := by
          refine ⟨?_, hv.2⟩
          intro e he
          exact hv.1 e (by simp [he])
        by_cases hab : a = b
        · subst b
          simp only [List.map_cons, loopyAux, ↓reduceIte]
          apply ih g V (addLoop ell a)
          refine ⟨htail.1, ?_⟩
          intro v hvv
          have hva : v ≠ a := fun h => hvv (h ▸ (hv.1 (a, a) (by simp)).1)
          simp [addLoop, hva, hv.2 v hvv]
        · have hc := ih (contractEdge a b ∘ g) (V.erase b)
              (contractLoops ell a b)
              (by
                have hcv := hcontractValid V (l₁.map g) ell a b hv hab
                rw [List.map_map] at hcv
                exact hcv)
          have hd := ih g V ell htail
          simp only [List.map_cons, loopyAux, hab, if_false, List.map_map,
            Function.comp_apply, contractEdge, Prod.fst, Prod.snd]
          rw [hc, hd]
    | swap x y l =>
        intro g V ell hv
        have hs := hswap V (l.map g) ell (g y) (g x) hv
        rw [loopy, loopy] at hs
        exact hs
    | trans hp hq ihp ihq =>
        intro g V ell hv
        exact (ihp g V ell hv).trans
          (ihq g V ell (hvalidPerm V _ _ ell (hp.map g) hv))
  have hpermAux : ∀ (V : Finset Nat) (E E' : List Edge) (ell : Nat → Nat),
      E.Perm E' → Valid V E ell →
        loopyAux V E ell = loopyAux V E' ell := by
    intro V E E' ell hp hv
    simpa using hpermMap E E' hp (fun e => e) V ell (by simpa using hv)
  have hperm : ∀ (V : Finset Nat) (E E' : List Edge) (ell : Nat → Nat),
      E.Perm E' → Valid V E ell → loopy V E ell = loopy V E' ell := by
    intro V E E' ell hp hv
    rw [loopy, loopy]
    exact hpermAux V E E' ell hp hv
  have hrec : ∀ (V : Finset Nat) (E R : List Edge) (ell : Nat → Nat)
      (e : Edge), E.Perm (e :: R) → Valid V E ell →
        loopy V E ell =
          if e.1 = e.2 then loopy V R (addLoop ell e.1)
          else loopy (V.erase e.2) (R.map (contractEdge e.1 e.2))
              (contractLoops ell e.1 e.2) +
            MvPolynomial.C Polynomial.X * loopy V R ell := by
    intro V E R ell e hp hv
    rw [hperm V E (e :: R) ell hp hv]
    rcases e with ⟨a, b⟩
    by_cases hab : a = b
    · subst b
      simp only [loopy, loopyAux, ↓reduceIte]
    · simp only [loopy, loopyAux, hab, if_false]
  have unionCore : ∀ n : Nat, ∀ (V₁ V₂ : Finset Nat) (E₁ E₂ : List Edge)
      (ell₁ ell₂ : Nat → Nat), E₁.length + E₂.length = n →
      Disjoint V₁ V₂ → Valid V₁ E₁ ell₁ → Valid V₂ E₂ ell₂ →
      loopyAux (V₁ ∪ V₂) (E₁ ++ E₂) (unionLoops ell₁ ell₂) =
        loopyAux V₁ E₁ ell₁ * loopyAux V₂ E₂ ell₂ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        -- A nonempty factor supplies the recursive edge; the other factor is
        -- fixed by contraction because both endpoints lie in the first carrier.
        have step (V₁ V₂ : Finset Nat) (R E₂ : List Edge) (ell₁ ell₂ : Nat → Nat)
            (a b : Nat) (hlen : ((a, b) :: R).length + E₂.length = n)
            (hdisj : Disjoint V₁ V₂) (hv₁ : Valid V₁ ((a, b) :: R) ell₁)
            (hv₂ : Valid V₂ E₂ ell₂) :
            loopyAux (V₁ ∪ V₂) (((a, b) :: R) ++ E₂) (unionLoops ell₁ ell₂) =
              loopyAux V₁ ((a, b) :: R) ell₁ * loopyAux V₂ E₂ ell₂ := by
          have haV := (hv₁.1 (a, b) (by simp)).1
          have hbV := (hv₁.1 (a, b) (by simp)).2
          have ha₂ : a ∉ V₂ := Finset.disjoint_left.mp hdisj haV
          have hb₂ : b ∉ V₂ := Finset.disjoint_left.mp hdisj hbV
          have htail : Valid V₁ R ell₁ := by
            exact ⟨fun e he => hv₁.1 e (by simp [he]), hv₁.2⟩
          have hlt : R.length + E₂.length < n := by
            simp only [List.length_cons] at hlen
            omega
          by_cases hab : a = b
          · subst b
            have hadd : Valid V₁ R (addLoop ell₁ a) := by
              refine ⟨htail.1, ?_⟩
              intro v hv
              have hva : v ≠ a := fun h => hv (h ▸ haV)
              simp [addLoop, hva, hv₁.2 v hv]
            have hloops : addLoop (unionLoops ell₁ ell₂) a =
                unionLoops (addLoop ell₁ a) ell₂ := by
              funext v
              by_cases hva : v = a <;> simp [addLoop, unionLoops, hva] <;> omega
            simp only [List.cons_append, loopyAux, ↓reduceIte]
            rw [hloops]
            exact ih (R.length + E₂.length) hlt V₁ V₂ R E₂
              (addLoop ell₁ a) ell₂ rfl hdisj hadd hv₂
          · have hc := hcontractValid V₁ R ell₁ a b hv₁ hab
            have hdc : Disjoint (V₁.erase b) V₂ := by
              apply Finset.disjoint_left.mpr
              intro v hv
              exact Finset.disjoint_left.mp hdisj (Finset.mem_erase.mp hv).2
            have hvertices : (V₁ ∪ V₂).erase b = V₁.erase b ∪ V₂ := by
              rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hb₂]
            have hmap₂ : E₂.map (contractEdge a b) = E₂ := by
              calc
                E₂.map (contractEdge a b) = E₂.map (fun e => e) := by
                  apply List.map_congr_left
                  intro e he
                  have heV := hv₂.1 e he
                  have hfst : e.1 ≠ b := fun h => hb₂ (h ▸ heV.1)
                  have hsnd : e.2 ≠ b := fun h => hb₂ (h ▸ heV.2)
                  simp [contractEdge, contractVertex, hfst, hsnd]
                _ = E₂ := by simp
            have hloops : contractLoops (unionLoops ell₁ ell₂) a b =
                unionLoops (contractLoops ell₁ a b) ell₂ := by
              have hza := hv₂.2 a ha₂
              have hzb := hv₂.2 b hb₂
              funext v
              by_cases hva : v = a
              · subst v
                simp [contractLoops, unionLoops, hza, hzb]
              · by_cases hvb : v = b
                · subst v
                  simp [contractLoops, unionLoops, hva, hzb]
                · simp [contractLoops, unionLoops, hva, hvb]
            have hcontract := ih ((R.map (contractEdge a b)).length + E₂.length)
              (by simpa using hlt) (V₁.erase b) V₂ (R.map (contractEdge a b)) E₂
              (contractLoops ell₁ a b) ell₂ rfl hdc hc hv₂
            have hdelete := ih (R.length + E₂.length) hlt V₁ V₂ R E₂
              ell₁ ell₂ rfl hdisj htail hv₂
            simp only [List.cons_append, loopyAux, if_neg hab]
            rw [hvertices, List.map_append, hmap₂, hloops, hcontract, hdelete]
            ring
        intro V₁ V₂ E₁ E₂ ell₁ ell₂ hlen hdisj hv₁ hv₂
        cases E₁ with
        | cons e R =>
            rcases e with ⟨a, b⟩
            exact step V₁ V₂ R E₂ ell₁ ell₂ a b hlen hdisj hv₁ hv₂
        | nil =>
            cases E₂ with
            | nil =>
                simp only [List.nil_append, loopyAux]
                rw [Finset.prod_union hdisj]
                congr 1
                · apply Finset.prod_congr rfl
                  intro v hv
                  have hz := hv₂.2 v (Finset.disjoint_left.mp hdisj hv)
                  simp [unionLoops, hz]
                · apply Finset.prod_congr rfl
                  intro v hv
                  have hz := hv₁.2 v (Finset.disjoint_right.mp hdisj hv)
                  simp [unionLoops, hz]
            | cons e R =>
                rcases e with ⟨a, b⟩
                have hlen' : ((a, b) :: R).length + ([] : List Edge).length = n := by
                  simpa [Nat.add_comm] using hlen
                have hs := step V₂ V₁ R [] ell₂ ell₁ a b hlen' hdisj.symm hv₂ hv₁
                have hloops : unionLoops ell₂ ell₁ = unionLoops ell₁ ell₂ := by
                  funext v
                  exact Nat.add_comm _ _
                simpa only [List.append_nil, List.nil_append, Finset.union_comm,
                  hloops, mul_comm] using hs
  exact ⟨hrelabel, horient, hswap, hloop, hperm, hrec,
    fun V₁ V₂ E₁ E₂ ell₁ ell₂ => unionCore (E₁.length + E₂.length)
      V₁ V₂ E₁ E₂ ell₁ ell₂ rfl⟩
end
end D5.S3.Factorization.Combinatorics.LoopyDegreeSequence
