/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47TypeI
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47TypeI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional simultaneous type-I reconstruction from actual scalar PRODUCT coverage. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47Forest

set_option autoImplicit false
namespace NikolovSegal
namespace Equation47
universe u
variable {S I : Type u} [Group S] [DecidableEq I] {m : ℕ}

private theorem interval_split (J : Finset (Fin m))
    (hne : J.Nonempty) (hJ : ConsecutiveInterval J) :
    ∃ P Q R : List (Fin m), List.finRange m = P ++ Q ++ R ∧
      (∀ j ∈ P, j ∉ J) ∧ (∀ j ∈ Q, j ∈ J) ∧ (∀ j ∈ R, j ∉ J) := by
  let lo := (J.min' hne).val
  let hi := (J.max' hne).val + 1
  have hle : lo ≤ hi := by
    have hh := J.min'_le_max' hne
    change (J.min' hne).val ≤ (J.max' hne).val at hh
    dsimp [lo,hi]
    omega
  let P := (List.finRange m).take lo
  let Q := ((List.finRange m).drop lo).take (hi-lo)
  let R := (List.finRange m).drop hi
  refine ⟨P,Q,R,?_,?_,?_,?_⟩
  · dsimp [P,Q,R]
    rw [← List.take_add, Nat.add_sub_of_le hle,
      List.take_append_drop]
  · intro j hj hjJ
    obtain ⟨i,hi',heq⟩ := List.mem_take_iff_getElem.mp hj
    have hval : i = j.val := by simpa using congrArg Fin.val heq
    have hmin := J.min'_le j hjJ
    change lo ≤ j.val at hmin
    have hlow : i < lo := lt_of_lt_of_le hi' (Nat.min_le_left _ _)
    omega
  · intro j hj
    obtain ⟨i,hi',heq⟩ := List.mem_take_iff_getElem.mp hj
    have hval : lo + i = j.val := by
      simpa using congrArg Fin.val heq
    apply hJ (a := J.min' hne) (b := J.max' hne) (c := j)
      (J.min'_mem hne) (J.max'_mem hne)
    · change lo ≤ j.val
      omega
    · change j.val ≤ (J.max' hne).val
      have hil : i < hi-lo := lt_of_lt_of_le hi' (Nat.min_le_left _ _)
      dsimp [hi] at hil
      omega
  · intro j hj hjJ
    obtain ⟨i,hi',heq⟩ := List.mem_drop_iff_getElem.mp hj
    have hval : hi + i = j.val := by
      simpa using congrArg Fin.val heq
    have hmax := J.le_max' j hjJ
    change j.val ≤ (J.max' hne).val at hmax
    dsimp [hi] at hval
    omega

private theorem interval_splice (J : Finset (Fin m))
    (hne : J.Nonempty) (hJ : ConsecutiveInterval J) (f : Fin m → S) :
    ∃ A B : S, ∀ s : Fin m → S, (∀ j, j ∉ J → s j = 1) →
      orderedProduct (fun j => if j ∈ J then s j else f j) =
        A * orderedProduct s * B := by
  obtain ⟨P,Q,R,hlist,hP,hQ,hR⟩ := interval_split J hne hJ
  refine ⟨(P.map f).prod,(R.map f).prod,?_⟩
  intro s hs
  have hpre : (P.map (fun j => if j ∈ J then s j else f j)) = P.map f := by
    apply List.map_congr_left
    intro j hj
    simp [hP j hj]
  have hmid : (Q.map (fun j => if j ∈ J then s j else f j)) = Q.map s := by
    apply List.map_congr_left
    intro j hj
    simp [hQ j hj]
  have hpost : (R.map (fun j => if j ∈ J then s j else f j)) = R.map f := by
    apply List.map_congr_left
    intro j hj
    simp [hR j hj]
  have hPone : (P.map s).prod = 1 := by
    apply List.prod_eq_one
    intro z hz
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
    exact hs j (hP j hj)
  have hRone : (R.map s).prod = 1 := by
    apply List.prod_eq_one
    intro z hz
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
    exact hs j (hR j hj)
  simp only [orderedProduct, List.ofFn_eq_map, hlist, List.map_append,
    List.prod_append, hpre, hmid, hpost, hPone, hRone, one_mul, mul_one]

theorem fill_typeI_root
    (τ : Fin m → Equiv.Perm I) (α : Fin m → I → MulAut S)
    (a : Arc m I → S) (root : I) (sel J : Finset (Fin m))
    (hsub : sel ⊆ J) (hne : J.Nonempty) (hJ : ConsecutiveInterval J)
    (hfix : ∀ j ∈ J, τ j root = root)
    (ha : ∀ j ∈ J, a (j,root) = 1)
    (hscalar : ∀ t : S, ∃ x : Fin m → S,
      (∀ j, j ∉ sel → x j = 1) ∧
      orderedProduct (fun j => (x j)⁻¹ * α j root (x j)) = t)
    (target : S) :
    ∃ z : Arc m I → S, vertex τ α z root = target ∧
      (∀ v, v ≠ root → vertex τ α z v = vertex τ α a v) ∧
      (∀ e, e.2 ≠ root ∨ e.1 ∉ sel → z e = a e) := by
  classical
  let f : Fin m → S := fun j =>
    (a (j,root))⁻¹ * α j ((τ j).symm root) (a (j,(τ j).symm root))
  obtain ⟨A,B,hAB⟩ := interval_splice J hne hJ f
  obtain ⟨x,hx,hprod⟩ := hscalar (A⁻¹ * target * B⁻¹)
  let z : Arc m I → S := fun e =>
    if e.2 = root ∧ e.1 ∈ sel then x e.1 else a e
  have hz : ∀ e, e.2 ≠ root ∨ e.1 ∉ sel → z e = a e := by
    intro e he
    simp only [z]
    rcases he with he | he <;> simp [he]
  have hsymm : ∀ j ∈ J, (τ j).symm root = root := by
    intro j hj
    exact (τ j).injective (by simpa using (hfix j hj).symm)
  have hterm : ∀ j,
      (z (j,root))⁻¹ * α j ((τ j).symm root) (z (j,(τ j).symm root)) =
        if j ∈ J then (x j)⁻¹ * α j root (x j) else f j := by
    intro j
    by_cases hj : j ∈ J
    · rw [if_pos hj, hsymm j hj]
      by_cases hs : j ∈ sel
      · simp [z,hs]
      · simp [z,hs,hx j hs,ha j hj]
    · have hs : j ∉ sel := fun hs => hj (hsub hs)
      have hin : (τ j).symm root ≠ root ∨ j ∉ sel := Or.inr hs
      rw [if_neg hj,hz (j,root) (Or.inr hs),hz (j,(τ j).symm root) hin]
  refine ⟨z,?_,?_,hz⟩
  · unfold vertex
    rw [show (fun j => (z (j,root))⁻¹ *
      α j ((τ j).symm root) (z (j,(τ j).symm root))) =
      (fun j => if j ∈ J then (x j)⁻¹ * α j root (x j) else f j)
      from funext hterm]
    rw [hAB _ (by intro j hj; simp [hx j (fun hs => hj (hsub hs))]), hprod]
    simp [mul_assoc]
  · intro v hv
    unfold vertex
    congr 1
    funext j
    have hneg := hz (j,v) (Or.inl hv)
    have hpos : z (j,(τ j).symm v) = a (j,(τ j).symm v) := by
      by_cases hj : j ∈ sel
      · apply hz
        left
        intro he
        apply hv
        have hh := congrArg (τ j) he
        simpa [hfix j (hsub hj)] using hh
      · exact hz _ (Or.inr hj)
    rw [hneg,hpos]

private theorem fill_roots
    (τ : Fin m → Equiv.Perm I) (α : Fin m → I → MulAut S)
    (sel J : I → Finset (Fin m)) (κ : I → S) (K : Finset I)
    (hsub : ∀ v ∈ K, sel v ⊆ J v)
    (hne : ∀ v ∈ K, (J v).Nonempty)
    (hJ : ∀ v ∈ K, ConsecutiveInterval (J v))
    (hfix : ∀ v ∈ K, ∀ j ∈ J v, τ j v = v)
    (hscalar : ∀ v ∈ K, ∀ t : S, ∃ x : Fin m → S,
      (∀ j, j ∉ sel v → x j = 1) ∧
      orderedProduct (fun j => (x j)⁻¹ * α j v (x j)) = t)
    (a : Arc m I → S) (ha : ∀ v ∈ K, ∀ j ∈ J v, a (j,v) = 1) :
    ∃ z : Arc m I → S,
      (∀ v ∈ K, vertex τ α z v = κ v) ∧
      (∀ v, v ∉ K → vertex τ α z v = vertex τ α a v) ∧
      (∀ e, e.2 ∉ K → z e = a e) := by
  classical
  induction K using Finset.induction_on generalizing a with
  | empty => exact ⟨a,by simp,by simp,by simp⟩
  | @insert v K hv ih =>
    obtain ⟨b,hb,hother,hunused⟩ := ih
      (fun w hw => hsub w (by simp [hw]))
      (fun w hw => hne w (by simp [hw]))
      (fun w hw => hJ w (by simp [hw]))
      (fun w hw => hfix w (by simp [hw]))
      (fun w hw => hscalar w (by simp [hw])) a
      (fun w hw => ha w (by simp [hw]))
    have hbv : ∀ j ∈ J v, b (j,v) = 1 := by
      intro j hj
      rw [hunused (j,v) hv]
      exact ha v (by simp) j hj
    obtain ⟨z,hzv,hzother,hzunused⟩ := fill_typeI_root τ α b v (sel v) (J v)
      (hsub v (by simp)) (hne v (by simp)) (hJ v (by simp))
      (hfix v (by simp)) hbv (hscalar v (by simp)) (κ v)
    refine ⟨z,?_,?_,?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hzv
      · rw [hzother w (fun h => hv (h ▸ hw))]
        exact hb w hw
    · intro w hw
      have hw' : w ≠ v ∧ w ∉ K := by simpa using hw
      rw [hzother w hw'.1,hother w hw'.2]
    · intro e he
      have he' : e.2 ≠ v ∧ e.2 ∉ K := by simpa using he
      rw [hzunused e (Or.inl he'.1),hunused e he'.2]

theorem actual_typeI_components_reconstruction
    [Fintype I] {q : ℕ}
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (y : Fin m → I → S) (r : I → I)
    (hr : ∀ v, (qPowerGraph σ q).Reachable (r v) v)
    (hconst : ∀ v w, (qPowerGraph σ q).Reachable v w → r v = r w)
    (sel J : I → Finset (Fin m))
    (hsub : ∀ v, v = r v → sel v ⊆ J v)
    (hne : ∀ v, v = r v → (J v).Nonempty)
    (hJ : ∀ v, v = r v → ConsecutiveInterval (J v))
    (hfix : ∀ v, v = r v → ∀ j ∈ J v, (σ j ^ q) v = v)
    (hscalar : ∀ v, v = r v → ∀ t : S, ∃ x : Fin m → S,
      (∀ j, j ∉ sel v → x j = 1) ∧
      orderedProduct (fun j => (x j)⁻¹ *
        correctedCycleComponent β σ y j v q (x j)) = t) :
    ∀ κ : I → S, ∃ c : Fin m → I → S,
      ∀ v, orderedProduct (fun j => (c j v)⁻¹ *
        (((k j * MulAut.conj (y j)⁻¹) ^ q) (c j)) v) = κ v := by
  classical
  obtain ⟨F,L,hF,hacyc,hgraph,hL,hmem,hedge⟩ :=
    exists_actual_leafOrder σ r hr hconst
  intro κ
  let τ : Fin m → Equiv.Perm I := fun j => σ j ^ q
  let α : Fin m → I → MulAut S := fun j i => correctedCycleComponent β σ y j i q
  let a : Arc m I → S := eliminate τ α κ L (fun _ => 1)
  let K := Finset.univ.filter (fun v => v = r v)
  have hK : ∀ v, v ∈ K ↔ v = r v := by simp [K]
  have ha : ∀ v ∈ K, ∀ j ∈ J v, a (j,v) = 1 := by
    intro v hv j hj
    exact eliminate_loop τ α κ L hL _ (j,v) (hfix v ((hK v).mp hv) j hj)
  obtain ⟨z,hroot,hother,hunused⟩ := fill_roots τ α sel J κ K
    (fun v hv => hsub v ((hK v).mp hv))
    (fun v hv => hne v ((hK v).mp hv))
    (fun v hv => hJ v ((hK v).mp hv))
    (fun v hv => hfix v ((hK v).mp hv))
    (fun v hv => hscalar v ((hK v).mp hv)) a ha
  refine ⟨fun j i => z (j,i),?_⟩
  intro v
  rw [← actual_vertex k σ β hcoord y (fun j i => z (j,i)) v]
  by_cases hv : v ∈ K
  · exact hroot v hv
  · rw [hother v hv]
    obtain ⟨p,hp,hpv⟩ := (hmem v).mpr (fun heq => hv ((hK v).mpr heq))
    rw [← hpv]
    exact eliminate_solves τ α κ L hL (fun _ => 1) p hp

theorem selected_support_scalar
    {q : ℕ}
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (y : Fin m → I → S) (root : I) (sel J : Finset (Fin m))
    (hsub : sel ⊆ J) (hfix : ∀ j ∈ J, (σ j ^ q) root = root)
    (hy : ∀ t : S, ∃ b : Fin m → I → S,
      orderedProduct (fun j => fun i => (b j i)⁻¹ *
        (((k j * MulAut.conj (y j)⁻¹) ^ q) (b j)) i) =
          (fun i => if i = root then t else 1) ∧
      (∀ j i, j ∉ sel ∨ i ≠ root → b j i = 1)) :
    ∀ t : S, ∃ x : Fin m → S,
      (∀ j, j ∉ sel → x j = 1) ∧
      orderedProduct (fun j => (x j)⁻¹ *
        correctedCycleComponent β σ y j root q (x j)) = t := by
  intro t
  obtain ⟨b,hb,hsupport⟩ := hy t
  refine ⟨fun j => b j root,fun j hj => hsupport j root (Or.inl hj),?_⟩
  have heval : (orderedProduct (fun j => fun i => (b j i)⁻¹ *
      (((k j * MulAut.conj (y j)⁻¹) ^ q) (b j)) i)) root =
      orderedProduct (fun j => (b j root)⁻¹ *
      (((k j * MulAut.conj (y j)⁻¹) ^ q) (b j)) root) := by
    simpa [orderedProduct,List.map_ofFn,Function.comp_def] using
      (map_list_prod (Pi.evalMonoidHom (fun _ : I => S) root)
        (List.ofFn (fun j => fun i => (b j i)⁻¹ *
          (((k j * MulAut.conj (y j)⁻¹) ^ q) (b j)) i)))
  have htarget := congrArg (fun z : I → S => z root) hb
  rw [heval] at htarget
  simp only [if_pos rfl] at htarget
  have hterm : ∀ j, (b j root)⁻¹ *
      correctedCycleComponent β σ y j root q (b j root) =
      (b j root)⁻¹ * (((k j * MulAut.conj (y j)⁻¹) ^ q) (b j)) root := by
    intro j
    by_cases hj : j ∈ sel
    · have h := actual_corrected_q_power_coordinate k σ β hcoord y j root q (b j)
      rw [hfix j (hsub hj)] at h
      rw [h]
    · have hb1 : b j = 1 := by
        funext i
        exact hsupport j i (Or.inl hj)
      simp [hb1]
  rw [show (fun j => (b j root)⁻¹ *
      correctedCycleComponent β σ y j root q (b j root)) =
      (fun j => (b j root)⁻¹ *
        (((k j * MulAut.conj (y j)⁻¹) ^ q) (b j)) root) from funext hterm]
  exact htarget

theorem actual_all_typeI_from_interval
    [Fintype I] {q D M : ℕ}
    (hq : 0 < q) (hD : 0 < D) (hM : 0 < M) (hm : M * D * (q+D) ≤ m)
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (rep : (qPowerGraph σ q).ConnectedComponent → I)
    (hrep : ∀ C, (qPowerGraph σ q).connectedComponentMk (rep C) = C)
    (good : Fin m → I → Prop) [∀ j, DecidablePred (good j)]
    (hperiod : ∀ j i, good j i → Function.IsPeriodicPt (σ j) q i)
    (hbad : ∀ C,
      (Finset.univ.filter (fun j : Fin m => ¬ good j (rep C))).card < D)
    (hscalar : ∀ (sel : (qPowerGraph σ q).ConnectedComponent → Finset (Fin m)),
      (hcard : ∀ C, (sel C).card = M) →
      (∀ C j, j ∈ sel C → good j (rep C)) →
      ∀ C, PartIIScalarProductInput q M
        (fun t : Fin M => cycleComponent β σ ((sel C).orderEmbOfFin (hcard C) t) (rep C)
          (Function.minimalPeriod (σ ((sel C).orderEmbOfFin (hcard C) t)) (rep C)))
        (fun t : Fin M => Function.minimalPeriod
          (σ ((sel C).orderEmbOfFin (hcard C) t)) (rep C))) :
    PrescribedCommutatorCoverage (I → S) q m k := by
  classical
  let G := qPowerGraph σ q
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hinj : Function.Injective rep := by
    intro C E h
    have hh := congrArg G.connectedComponentMk h
    change (qPowerGraph σ q).connectedComponentMk (rep C) =
      (qPowerGraph σ q).connectedComponentMk (rep E) at hh
    simpa only [hrep] using hh
  obtain ⟨tag,Iset,hI,hinterval,hgood,y,hy⟩ := actual_selected_interval_with_support
    hq hD hM hm rep hinj good σ hperiod hbad k β hcoord hscalar
  let r : I → I := fun v => rep (G.connectedComponentMk v)
  let sel : I → Finset (Fin m) := fun v => Iset (G.connectedComponentMk v)
  let J : I → Finset (Fin m) := fun v =>
    prefixPiece good rep (G.connectedComponentMk v) (tag (G.connectedComponentMk v))
  have hr : ∀ v, G.Reachable (r v) v := fun v =>
    SimpleGraph.ConnectedComponent.exact (hrep (G.connectedComponentMk v))
  have hconst : ∀ v w, G.Reachable v w → r v = r w := by
    intro v w h
    exact congrArg rep (SimpleGraph.ConnectedComponent.sound h)
  have hsub : ∀ v, v = r v → sel v ⊆ J v := fun v _ => (hI _).1
  have hne : ∀ v, v = r v → (J v).Nonempty := by
    intro v hv
    obtain ⟨j,hj⟩ := Finset.card_pos.mp
      (show 0 < (sel v).card by rw [(hI _).2]; exact hM)
    exact ⟨j,hsub v hv hj⟩
  have hfix : ∀ v, v = r v → ∀ j ∈ J v, (σ j ^ q) v = v := by
    intro v hv j hj
    change v = rep (G.connectedComponentMk v) at hv
    rw [hv]
    have hp := hperiod j _ (hgood _ j hj)
    simpa only [Equiv.Perm.coe_pow] using hp.isFixedPt.eq
  have hscalar' : ∀ v, v = r v → ∀ t : S, ∃ x : Fin m → S,
      (∀ j, j ∉ sel v → x j = 1) ∧
      orderedProduct (fun j => (x j)⁻¹ *
        correctedCycleComponent β σ y j v q (x j)) = t := by
    intro v hv
    apply selected_support_scalar k σ β hcoord y v (sel v) (J v) (hsub v hv) (hfix v hv)
    intro t
    have hrepv : rep (G.connectedComponentMk v) = v := hv.symm
    simpa only [hrepv] using hy (G.connectedComponentMk v) t
  have hcov := actual_typeI_components_reconstruction k σ β hcoord y r hr hconst sel J
    hsub hne (fun v _ => hinterval _) hfix hscalar'
  refine ⟨y,?_⟩
  intro κ
  obtain ⟨c,hc⟩ := hcov κ
  refine ⟨c,?_⟩
  funext v
  have heval : (orderedProduct (fun j => (c j)⁻¹ *
      (((k j * MulAut.conj (y j)⁻¹) ^ q) (c j)))) v =
      orderedProduct (fun j => (c j v)⁻¹ *
        (((k j * MulAut.conj (y j)⁻¹) ^ q) (c j)) v) := by
    simpa [orderedProduct,List.map_ofFn,Function.comp_def] using
      (map_list_prod (Pi.evalMonoidHom (fun _ : I => S) v)
        (List.ofFn (fun j => (c j)⁻¹ *
          (((k j * MulAut.conj (y j)⁻¹) ^ q) (c j)))))
  exact heval.trans (hc v)

end Equation47
end NikolovSegal
