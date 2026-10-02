/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/Parity
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/Parity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/

/-
physical_signed_addition:
  proof_shape: content
  escape_witness: Local physicalMX: physicalM n j l * physicalX n j l = physicalX n j l * diagonal(physicalCasimir n j l), together with the live signed_stretched_endpoint_match endpoint equality and Jacobi column-propagation uniqueness; these are identities of the actual shared matrices.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.Parity
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
open D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Orthogonality
open D5.S3.Quantum.Algebra.ZeitlinSixJ.SpectralInverse
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse

lemma physical_signed_addition (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
    physicalX n j l=physicalZ n j l := by
  have sum_shifted_support (f : ℕ → ℝ) (n r d : ℕ) (hd : d≤r) (hr : r≤n)
      (hz : ∀ i, i < d ∨ r < i → f i=0) :
      (∑ t ∈ range (r-d+1),f (d+t))=∑ i ∈ range (n+1),f i := by
    have htrim : (∑ i ∈ range (r+1),f i)=∑ i ∈ range (n+1),f i := by
      apply sum_subset (range_mono (by omega))
      intro i _ hi
      apply hz
      have hi' : ¬i < r+1 := by simpa only [mem_range] using hi
      right
      omega
    have hlow : (∑ i ∈ range d,f i)=0 := by
      apply sum_eq_zero
      intro i hi
      exact hz i (Or.inl (mem_range.mp hi))
    rw [show r+1=d+(r-d+1) by omega,sum_range_add,hlow,zero_add] at htrim
    exact htrim
  have sixJ_flip_pair (a b c d e f : ℕ) :
      sixJ a b c d e f = sixJ d e c a b f := by
    have ha : admissible a b c d e f ↔ admissible d e c a b f := by
      unfold admissible
      tauto
    have hlo : lower a b c d e f = lower d e c a b f := by
      unfold lower
      ac_rfl
    have hup : upper a b c d e f = upper d e c a b f := by
      unfold upper
      rw [show d+e+a+b=a+b+d+e by omega, show e+c+b+f=b+c+e+f by omega,
        show c+d+f+a=c+a+f+d by omega]
    have ht (z : ℕ) : racahTerm a b c d e f z = racahTerm d e c a b f z := by
      unfold racahTerm
      rw [show d+e+a+b=a+b+d+e by omega, show e+c+b+f=b+c+e+f by omega,
        show c+d+f+a=c+a+f+d by omega]
      congr 1
      ring
    have hr : racahSum a b c d e f = racahSum d e c a b f := by
      simp only [racahSum, ← hlo, ← hup, ← ht]
    have hd : deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c =
        deltaSq d e c*deltaSq d b f*deltaSq a e f*deltaSq a b c := by ring
    simp only [sixJ, ← ha, ← hd, ← hr]
  have channel_last (n j l : ℕ) (hj : j ≤ n) (hl : l ≤ n) (hjl : j ≤ l) :
      channelLabel n j l (channelWidth n j l) = n+2*j := by
    unfold channelLabel channelBase channelWidth
    have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
    omega
  have channel_admissible (n j l t u : ℕ) (hj : j ≤ n)
      (hl : l ≤ n) (hjl : j ≤ l) (ht : t ≤ channelWidth n j l)
      (hu : u ≤ channelWidth n j l) :
      admissible n n (2*(l-j+u)) (2*j) (2*l) (channelLabel n j l t) := by
    have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
    unfold channelWidth at ht hu
    unfold channelLabel channelBase admissible triangle
    omega
  have normalizedSixJ_dual (a b u c d y : ℕ) :
      normalizedSixJ a b u c d y=normalizedSixJ a d y c b u := by
    have sixJ_flip_last (a b u c d y : ℕ) :
        sixJ a b u c d y=sixJ a d y c b u := by
      have sixJ_cycle_columns (a b c d e f : ℕ) :
          sixJ a b c d e f = sixJ c a b f d e := by
        have triangle_cycle (a b c : ℕ) : triangle a b c ↔ triangle c a b := by
          unfold triangle
          omega
        have deltaSq_cycle (a b c : ℕ) : deltaSq a b c = deltaSq c a b := by
          unfold deltaSq
          rw [show c+a-b=a+c-b by omega, show c+b-a=b+c-a by omega,
            show a+b-c=a+b-c by rfl, show c+a+b=a+b+c by omega]
          ring
        have ha : admissible a b c d e f ↔ admissible c a b f d e := by
          unfold admissible
          rw [← triangle_cycle a b c, ← triangle_cycle d e c,
            ← triangle_cycle a e f, ← triangle_cycle d b f]
          tauto
        have hlo : lower a b c d e f = lower c a b f d e := by
          unfold lower
          rw [show c+a+b=a+b+c by omega, show c+d+e=d+e+c by omega,
            show f+a+e=a+e+f by omega, show f+d+b=d+b+f by omega]
          ac_rfl
        have hup : upper a b c d e f = upper c a b f d e := by
          unfold upper
          rw [show c+a+f+d=c+a+f+d by rfl, show a+b+d+e=a+b+d+e by rfl,
            show b+c+e+f=b+c+e+f by rfl]
          ac_rfl
        have ht (z : ℕ) : racahTerm a b c d e f z = racahTerm c a b f d e z := by
          unfold racahTerm
          rw [show c+a+b=a+b+c by omega, show c+d+e=d+e+c by omega,
            show f+a+e=a+e+f by omega, show f+d+b=d+b+f by omega]
          congr 1
          ring
        have hr : racahSum a b c d e f = racahSum c a b f d e := by
          simp only [racahSum, ← hlo, ← hup, ← ht]
        have hd : deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c =
            deltaSq c a b*deltaSq c d e*deltaSq f a e*deltaSq f d b := by
          rw [← deltaSq_cycle a b c, ← deltaSq_cycle d e c,
            ← deltaSq_cycle a e f, ← deltaSq_cycle d b f]
          ring
        simp only [sixJ, ← ha, ← hd, ← hr]
      calc
        _ = sixJ u a b y c d := sixJ_cycle_columns a b u c d y
        _ = sixJ b u a d y c := sixJ_cycle_columns u a b y c d
        _ = sixJ d y a b u c := sixJ_flip_pair b u a d y c
        _ = sixJ a d y c b u := sixJ_cycle_columns d y a b u c
    unfold normalizedSixJ
    rw [sixJ_flip_last]
    congr 1
    congr 1
    ring
  have normalizedSixJ_zero (a b u c d y : ℕ) (h : ¬admissible a b u c d y) :
      normalizedSixJ a b u c d y=0 := by
    simp only [normalizedSixJ,sixJ,if_neg h,mul_zero]
  have finiteSixJJacobi_edge (a b c d base m : ℕ) (t : Fin m) :
      finiteSixJJacobi a b c d base m t.castSucc t.succ=normalizedUpper a b c d (base+2*t.val) := by
    have he : t.castSucc ≠ t.succ := by intro h; have hv := congrArg Fin.val h; simp at hv
    have hbad : ¬t.val+1+1=t.val := by omega
    simp [finiteSixJJacobi,jacobiMatrix,upperBand,Matrix.diagonal,he,hbad]
  have physicalT_edge_positive (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l)
      (t : Fin (channelWidth n j l)) : 0 < physicalT n j l t.castSucc t.succ := by
    have recurrence_upper_positive (a b u c d y : ℕ)
        (had : admissible a b u c d y) (hp : admissible a b u c d (y+2)) :
        0 < recurrenceUpperCoefficient a b c d y := by
      have raising_factors_positive (a b u c d y : ℕ)
          (had : admissible a b u c d y) (hp : admissible a b u c d (y+2)) :
          0 < raisingNumerator a b c d y ∧ 0 < raisingDenominator a b c d y := by
        have deltaSq_raise_factors_positive (a b c : ℕ) (ht : triangle a b c)
            (hi : c+2 ≤ a+b) :
            (0 : ℚ) < ((c : ℚ)/2+1)^2-(((a : ℚ)-b)/2)^2 ∧
              (0 : ℚ) < (((a : ℚ)+b)/2+1)^2-((c : ℚ)/2+1)^2 := by
          have triangle_difference_halves (a b c : ℕ) (ht : triangle a b c) :
              ((((a+b-c)/2 : ℕ) : ℚ) = ((a : ℚ)+b-c)/2) ∧
              ((((a+c-b)/2 : ℕ) : ℚ) = ((a : ℚ)+c-b)/2) ∧
              ((((b+c-a)/2 : ℕ) : ℚ) = ((b : ℚ)+c-a)/2) ∧
              ((((a+b+c)/2 : ℕ) : ℚ) = ((a : ℚ)+b+c)/2) := by
            have half_cast (n : ℕ) (hn : n % 2 = 0) :
                (((n/2 : ℕ) : ℤ) : ℚ) = (n : ℚ)/2 := by
              have he : 2*(n/2) = n := by omega
              have hq := congrArg (fun k : ℕ => (k : ℚ)) he
              simp only [Nat.cast_mul, Nat.cast_ofNat] at hq
              simp only [Int.cast_natCast]
              apply (eq_div_iff (by positivity : (2 : ℚ) ≠ 0)).mpr
              simpa only [mul_comm] using hq
            rcases ht with ⟨ha,hb,hc,hp⟩
            have hp1 : (a+b-c)%2=0 := by omega
            have hp2 : (a+c-b)%2=0 := by omega
            have hp3 : (b+c-a)%2=0 := by omega
            have h1 := half_cast (a+b-c) hp1
            have h2 := half_cast (a+c-b) hp2
            have h3 := half_cast (b+c-a) hp3
            have h4 := half_cast (a+b+c) hp
            simp only [Int.cast_natCast,Nat.cast_sub hc,Nat.cast_sub hb,Nat.cast_sub ha,Nat.cast_add] at *
            exact ⟨h1,h2,h3,h4⟩
          rcases triangle_difference_halves a b c ht with ⟨h1,h2,h3,h4⟩
          have h1p : (0 : ℚ) < (((a+b-c)/2 : ℕ) : ℚ) := by
            exact_mod_cast (by omega : 0 < (a+b-c)/2)
          have h2p : (0 : ℚ) < (((a+c-b)/2 : ℕ) : ℚ)+1 := by positivity
          have h3p : (0 : ℚ) < (((b+c-a)/2 : ℕ) : ℚ)+1 := by positivity
          have h4p : (0 : ℚ) < (((a+b+c)/2 : ℕ) : ℚ)+2 := by positivity
          rw [h1] at h1p
          rw [h2] at h2p
          rw [h3] at h3p
          rw [h4] at h4p
          constructor
          · have h := mul_pos h2p h3p
            convert h using 1 <;> first | rfl | ring
          · have h := mul_pos h1p h4p
            convert h using 1 <;> first | rfl | ring
        have ha := deltaSq_raise_factors_positive a d y had.2.1 hp.2.1.2.2.1
        have hb := deltaSq_raise_factors_positive c b y had.2.2.1 hp.2.2.1.2.2.1
        constructor
        · unfold raisingNumerator
          have h := mul_pos ha.1 hb.1
          convert h using 1 <;> first | rfl | ring
        · unfold raisingDenominator
          have h := mul_pos ha.2 hb.2
          convert h using 1 <;> first | rfl | ring
      have hpos := raising_factors_positive a b u c d y had hp
      unfold recurrenceUpperCoefficient
      apply div_pos
      · apply Real.sqrt_pos.mpr
        exact_mod_cast mul_pos hpos.1 hpos.2
      · push_cast
        positivity
    rw [physicalT,finiteSixJJacobi_edge]
    unfold normalizedUpper
    apply div_pos
    · apply mul_pos
      · refine recurrence_upper_positive n n (2*(l-j)) (2*j) (2*l) (channelBase n j l+2*t.val) ?_ ?_
        · exact channel_admissible n j l t.val 0 hj hl hjl (by omega) (by omega)
        · have ha := channel_admissible n j l (t.val+1) 0 hj hl hjl (by omega) (by omega)
          have he : channelLabel n j l (t.val+1)=channelBase n j l+2*t.val+2 := by unfold channelLabel; omega
          simpa only [he,Nat.add_zero] using ha
      · positivity
    · positivity
  have physicalX_symmetric (n j l : ℕ) : (physicalX n j l)ᵀ=physicalX n j l := by
    unfold physicalX indexParity
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.diagonal_transpose,Matrix.transpose_transpose,
      Matrix.mul_assoc]
  have physicalMX (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
      physicalM n j l*physicalX n j l=physicalX n j l*diagonal (physicalCasimir n j l) := by
    have finiteSixJJacobi_symmetric (a b c d base m : ℕ) :
        (finiteSixJJacobi a b c d base m)ᵀ=finiteSixJJacobi a b c d base m := by
      have jacobiMatrix_symmetric (m : ℕ) (a e : Fin (m+1) → ℝ) :
          (jacobiMatrix m a e)ᵀ=jacobiMatrix m a e := by
        simp only [jacobiMatrix,Matrix.transpose_add,Matrix.diagonal_transpose,Matrix.transpose_transpose]
        abel
      exact jacobiMatrix_symmetric m _ _
    have physicalTU (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
        physicalT n j l*physicalU n j l=physicalU n j l*
          diagonal (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val)) := by
      have channel_below_missing (n j l u : ℕ) (hjl : j≤l)
          (hy : 2≤channelBase n j l) :
          normalizedSixJ n n u (2*j) (2*l) (channelBase n j l-2)=0 := by
        apply normalizedSixJ_zero
        intro ha
        by_cases hn : j+l≤n
        · have hb : channelBase n j l=n-2*j := by unfold channelBase; omega
          have h := ha.2.2.1.2.1
          rw [hb] at hy h
          omega
        · have hb : channelBase n j l=2*l-n := by unfold channelBase; omega
          have h := ha.2.1.2.1
          rw [hb] at hy h
          omega
      have channel_above_missing (n j l u : ℕ) :
          normalizedSixJ n n u (2*j) (2*l) (n+2*j+2)=0 := by
        apply normalizedSixJ_zero
        intro ha
        have h := ha.2.2.1.2.2.1
        omega
      have physicalU_finite (n j l : ℕ) :
          physicalU n j l=finiteSixJMatrix n n (2*j) (2*l) (channelBase n j l)
            (channelWidth n j l) (fun i : Fin (channelWidth n j l+1) => 2*(l-j+i.val)) := by
        exact rfl
      have he : channelBase n j l+2*channelWidth n j l+2=n+2*j+2 := by
        have h := channel_last n j l hj hl hjl
        unfold channelLabel at h
        omega
      have h := finiteSixJ_action n n (2*j) (2*l) (channelBase n j l) (channelWidth n j l)
        (fun i : Fin (channelWidth n j l+1) => 2*(l-j+i.val))
        (fun k i => channel_admissible n j l k.val i.val hj hl hjl
          (by omega) (by omega))
        (fun i hb => channel_below_missing n j l (2*(l-j+i.val)) hjl hb)
        (fun i => by rw [he]; exact channel_above_missing n j l (2*(l-j+i.val)))
      have hc : (fun i : Fin (channelWidth n j l+1) =>
          ((((2*(l-j+i.val) : ℕ) : ℚ)/2*(((2*(l-j+i.val) : ℕ) : ℚ)/2+1) : ℚ) : ℝ)) =
          fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val) := by
        funext i
        unfold casimir
        push_cast
        ring
      rw [hc,←physicalU_finite] at h
      exact h
    have physicalDU (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
        diagonal (physicalCasimir n j l)*physicalU n j l=physicalU n j l*physicalH n j l := by
      have admissible_flip_last (a b u c d y : ℕ) :
          admissible a b u c d y ↔ admissible a d y c b u := by
        unfold admissible
        tauto
      have physicalU_dual (n j l : ℕ) :
          (physicalU n j l)ᵀ=finiteSixJMatrix n (2*l) (2*j) n (2*(l-j))
            (channelWidth n j l) (fun k : Fin (channelWidth n j l+1) => channelLabel n j l k.val) := by
        ext i k
        change normalizedSixJ n n (2*(l-j+i.val)) (2*j) (2*l) (channelLabel n j l k.val) =
          normalizedSixJ n (2*l) (channelLabel n j l k.val) (2*j) n (2*(l-j)+2*i.val)
        have he : 2*(l-j+i.val)=2*(l-j)+2*i.val := by omega
        simpa only [he] using normalizedSixJ_dual n n (2*(l-j+i.val)) (2*j) (2*l) (channelLabel n j l k.val)
      have h := finiteSixJ_action n (2*l) (2*j) n (2*(l-j)) (channelWidth n j l)
        (fun k : Fin (channelWidth n j l+1) => channelLabel n j l k.val)
        (fun i k => by
          have ha := channel_admissible n j l k.val i.val hj hl hjl (by omega) (by omega)
          have he : 2*(l-j+i.val)=2*(l-j)+2*i.val := by omega
          rw [he] at ha
          exact (admissible_flip_last _ _ _ _ _ _).mp ha)
        (fun k hb => by
          apply normalizedSixJ_zero
          intro ha
          have hbad := ha.2.2.1.2.1
          omega)
        (fun k => by
          apply normalizedSixJ_zero
          intro ha
          have hn := ha.2.1.2.2.1
          have hp := ha.2.2.1.2.2.1
          unfold channelWidth at hn hp
          omega)
      rw [←physicalU_dual] at h
      have ht := congrArg Matrix.transpose h
      simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.diagonal_transpose,
        finiteSixJJacobi_symmetric] at ht
      exact ht.symm
    have physicalH_anticommutator (n j l : ℕ) (hjl : j≤l) :
        physicalH n j l*indexParity (channelWidth n j l) (l-j)+
          indexParity (channelWidth n j l) (l-j)*physicalH n j l=
            (physicalC0 n j l • (1 : Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ)-
              diagonal (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val)))*
                indexParity (channelWidth n j l) (l-j) := by
      have jacobi_parity_anticommutator (m b : ℕ) (a e : Fin (m+1) → ℝ) :
          jacobiMatrix m a e*indexParity m b+indexParity m b*jacobiMatrix m a e=
            diagonal (fun i => 2*a i*(-1 : ℝ)^(b+i.val)) := by
        classical
        ext i j
        simp only [indexParity,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.add_apply]
        by_cases he : i=j
        · subst j
          have hn : ¬i.val+1=i.val := by omega
          simp [jacobiMatrix,upperBand,Matrix.diagonal,hn]
          ring
        · have hev : i.val≠j.val := by intro h;exact he (Fin.ext h)
          by_cases hu : i.val+1=j.val
          · have hs : (-1 : ℝ)^(b+j.val)=-(-1 : ℝ)^(b+i.val) := by
              rw [show b+j.val=(b+i.val)+1 by omega,pow_succ]
              ring
            have hl : ¬j.val+1=i.val := by omega
            simp [jacobiMatrix,upperBand,Matrix.diagonal,he,hu,hl,hs]
            ring
          · by_cases hl : j.val+1=i.val
            · have hs : (-1 : ℝ)^(b+i.val)=-(-1 : ℝ)^(b+j.val) := by
                rw [show b+i.val=(b+j.val)+1 by omega,pow_succ]
                ring
              simp [jacobiMatrix,upperBand,Matrix.diagonal,he,hu,hl,hs]
              ring
            · simp [jacobiMatrix,upperBand,Matrix.diagonal,he,hu,hl]
      have dual_diagonal (n j l t : ℕ) (hjl : j≤l) :
          2*(recurrenceDiagonalQ n (2*l) (2*j) n (2*(l-j)+2*t) : ℝ)=
            physicalC0 n j l-casimir (l-j+t) := by
        have raw_dual_diagonal (s j l i : ℚ) (hi : i≠0) (hi1 : i+1≠0) :
            2*rawDiagonal s l j s i=2*spinCasimir s+spinCasimir j+spinCasimir l-spinCasimir i := by
          unfold rawDiagonal spinCasimir
          field_simp [hi,hi1]
          ring
        by_cases h0 : l-j+t=0
        · have he : j=l := by omega
          have ht : t=0 := by omega
          subst l; subst t
          simp only [Nat.sub_self,Nat.mul_zero,Nat.add_zero,recurrenceDiagonalQ,if_pos rfl]
          unfold physicalC0 casimir
          push_cast
          ring
        · have hp : 0<l-j+t := by omega
          have hy : 2*(l-j)+2*t≠0 := by omega
          have hh : (((2*(l-j)+2*t : ℕ) : ℚ)/2)=(l-j+t : ℕ) := by push_cast;ring
          have hjq : (((2*j : ℕ) : ℚ)/2)=(j : ℚ) := by push_cast;ring
          have hlq : (((2*l : ℕ) : ℚ)/2)=(l : ℚ) := by push_cast;ring
          have hpr : (0 : ℚ)<(l-j+t : ℕ) := by exact_mod_cast hp
          have h := raw_dual_diagonal ((n : ℚ)/2) j l ((l-j+t : ℕ) : ℚ) (ne_of_gt hpr) (by positivity)
          rw [recurrenceDiagonalQ,if_neg hy,hh,hjq,hlq]
          have hr := congrArg (fun q : ℚ => (q : ℝ)) h
          unfold physicalC0 casimir
          unfold spinCasimir at hr
          push_cast at hr ⊢
          convert hr using 1 <;> ring
      rw [physicalH,finiteSixJJacobi,jacobi_parity_anticommutator]
      rw [Matrix.smul_one_eq_diagonal,diagonal_sub,indexParity,diagonal_mul_diagonal]
      congr 1
      funext i
      rw [dual_diagonal n j l i.val hjl]
    have h := congrArg (fun A => physicalU n j l*A*(physicalU n j l)ᵀ)
      (physicalH_anticommutator n j l hjl)
    have hdual := congrArg Matrix.transpose (physicalDU n j l hj hl hjl)
    simp only [Matrix.transpose_mul,Matrix.diagonal_transpose,physicalH,finiteSixJJacobi_symmetric] at hdual
    change (physicalU n j l)ᵀ*diagonal (physicalCasimir n j l)=physicalH n j l*(physicalU n j l)ᵀ at hdual
    have hleft : physicalU n j l*(physicalH n j l*indexParity (channelWidth n j l) (l-j))*(physicalU n j l)ᵀ =
        diagonal (physicalCasimir n j l)*physicalX n j l := by
      unfold physicalX
      rw [←Matrix.mul_assoc,←physicalDU n j l hj hl hjl]
      simp only [Matrix.mul_assoc]
    have hright : physicalU n j l*(indexParity (channelWidth n j l) (l-j)*physicalH n j l)*(physicalU n j l)ᵀ =
        physicalX n j l*diagonal (physicalCasimir n j l) := by
      unfold physicalX
      simp only [Matrix.mul_assoc]
      rw [hdual]
    have hother : physicalU n j l*((physicalC0 n j l • 1-
        diagonal (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val)))*
          indexParity (channelWidth n j l) (l-j))*(physicalU n j l)ᵀ =
            physicalC0 n j l • physicalX n j l-physicalT n j l*physicalX n j l := by
      simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul]
      unfold physicalX
      simp only [←Matrix.mul_assoc]
      rw [←physicalTU n j l hj hl hjl]
    rw [Matrix.mul_add,Matrix.add_mul,hleft,hright,hother] at h
    unfold physicalM
    rw [Matrix.sub_mul,Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul]
    calc
      _ = (physicalC0 n j l • physicalX n j l-physicalT n j l*physicalX n j l)-
          diagonal (physicalCasimir n j l)*physicalX n j l := by abel
      _ = _ := by rw [←h]; abel
  have physicalM_jacobi (n j l : ℕ) : physicalM n j l=
      jacobiMatrix (channelWidth n j l)
        (fun k => physicalC0 n j l-physicalCasimir n j l k-
          (recurrenceDiagonalQ n n (2*j) (2*l) (channelLabel n j l k.val) : ℝ))
        (fun k => -normalizedUpper n n (2*j) (2*l) (channelLabel n j l k.val)) := by
    let m := channelWidth n j l
    let a : Fin (m+1) → ℝ := fun k => (recurrenceDiagonalQ n n (2*j) (2*l) (channelLabel n j l k.val) : ℝ)
    let e : Fin (m+1) → ℝ := fun k => normalizedUpper n n (2*j) (2*l) (channelLabel n j l k.val)
    change physicalC0 n j l • 1-diagonal (physicalCasimir n j l)-jacobiMatrix m a e=
      jacobiMatrix m (fun k => physicalC0 n j l-physicalCasimir n j l k-a k) (fun k => -e k)
    have hup : upperBand m (fun k => -e k)= -upperBand m e := by
      ext k h
      simp only [upperBand,Matrix.neg_apply]
      split_ifs <;> simp
    have hdiag : diagonal (fun k => physicalC0 n j l-physicalCasimir n j l k-a k)=
        diagonal (fun _ => physicalC0 n j l)-diagonal (physicalCasimir n j l)-diagonal a := by
      rw [diagonal_sub,diagonal_sub]
    unfold jacobiMatrix
    rw [hup,Matrix.transpose_neg,hdiag,Matrix.smul_one_eq_diagonal]
    abel
  have physicalZ_symmetric (n j l : ℕ) : (physicalZ n j l)ᵀ=physicalZ n j l := by
    have physicalV_symmetric (n j l : ℕ) : (physicalV n j l)ᵀ=physicalV n j l := by
      have normalizedSixJ_flip_pair (a b u c d y : ℕ) :
          normalizedSixJ a b u c d y=normalizedSixJ c d u a b y := by
        unfold normalizedSixJ
        rw [sixJ_flip_pair]
      ext k h
      change normalizedSixJ n (2*l) (channelLabel n j l k.val) n (2*j) (channelLabel n j l h.val) =
        normalizedSixJ n (2*l) (channelLabel n j l h.val) n (2*j) (channelLabel n j l k.val)
      rw [normalizedSixJ_dual,normalizedSixJ_flip_pair]
    unfold physicalZ indexParity
    rw [Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.diagonal_transpose,
      physicalV_symmetric,Matrix.mul_assoc]
  have physicalMZ (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
      physicalM n j l*physicalZ n j l=physicalZ n j l*diagonal (physicalCasimir n j l) := by
    have physicalTprimeV (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
        physicalTprime n j l*physicalV n j l=physicalV n j l*diagonal (physicalCasimir n j l) := by
      have he : channelBase n j l+2*channelWidth n j l+2=n+2*j+2 := by
        have h := channel_last n j l hj hl hjl
        unfold channelLabel at h
        omega
      apply finiteSixJ_action
      · intro k h
        have ha := channel_admissible n j l k.val 0 hj hl hjl (by omega) (by omega)
        have hb := channel_admissible n j l h.val 0 hj hl hjl (by omega) (by omega)
        unfold admissible triangle at ha hb ⊢
        unfold channelLabel at ha hb ⊢
        omega
      · intro h hy
        apply normalizedSixJ_zero
        intro ha
        by_cases hn : j+l≤n
        · have hb : channelBase n j l=n-2*j := by unfold channelBase;omega
          have hh := ha.2.1.1
          rw [hb] at hy hh
          omega
        · have hb : channelBase n j l=2*l-n := by unfold channelBase;omega
          have hh := ha.2.2.1.2.1
          rw [hb] at hy hh
          omega
      · intro h
        rw [he]
        apply normalizedSixJ_zero
        intro ha
        have hh := ha.2.1.2.2.1
        omega
    have physicalM_parity (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
        physicalM n j l*indexParity (channelWidth n j l) 0=
          indexParity (channelWidth n j l) 0*physicalTprime n j l := by
      have jacobi_parity_twist (m b : ℕ) (a e : Fin (m+1) → ℝ) :
          jacobiMatrix m a (fun i => -e i)*indexParity m b=
            indexParity m b*jacobiMatrix m a e := by
        classical
        ext i j
        simp only [indexParity,Matrix.mul_diagonal,Matrix.diagonal_mul]
        by_cases he : i=j
        · subst j
          have hn : ¬i.val+1=i.val := by omega
          simp [jacobiMatrix,upperBand,Matrix.diagonal,hn,mul_comm]
        · by_cases hu : i.val+1=j.val
          · have hs : (-1 : ℝ)^(b+j.val)=-(-1 : ℝ)^(b+i.val) := by
              rw [show b+j.val=(b+i.val)+1 by omega,pow_succ]
              ring
            have hl : ¬j.val+1=i.val := by omega
            simp [jacobiMatrix,upperBand,Matrix.diagonal,he,hu,hl,hs,mul_comm]
          · by_cases hl : j.val+1=i.val
            · have hs : (-1 : ℝ)^(b+i.val)=-(-1 : ℝ)^(b+j.val) := by
                rw [show b+i.val=(b+j.val)+1 by omega,pow_succ]
                ring
              simp [jacobiMatrix,upperBand,Matrix.diagonal,he,hu,hl,hs,mul_comm]
            · simp [jacobiMatrix,upperBand,Matrix.diagonal,he,hu,hl]
      have physicalTprime_jacobi (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
          physicalTprime n j l=jacobiMatrix (channelWidth n j l)
            (fun k => physicalC0 n j l-physicalCasimir n j l k-
              (recurrenceDiagonalQ n n (2*j) (2*l) (channelLabel n j l k.val) : ℝ))
            (fun k => normalizedUpper n n (2*j) (2*l) (channelLabel n j l k.val)) := by
        have star_edge_equal (n j l y : ℕ) :
            normalizedUpper n (2*l) n (2*j) y=normalizedUpper n n (2*j) (2*l) y := by
          have h : raisingNumerator n (2*l) n (2*j) y*raisingDenominator n (2*l) n (2*j) y=
              raisingNumerator n n (2*j) (2*l) y*raisingDenominator n n (2*j) (2*l) y := by
            unfold raisingNumerator raisingDenominator
            push_cast
            ring
          simp only [normalizedUpper,recurrenceUpperCoefficient,h]
        have star_diagonal_complement (n j l t : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l)
            (ht : t≤channelWidth n j l) :
            (recurrenceDiagonalQ n (2*l) n (2*j) (channelLabel n j l t) : ℝ) =
              physicalC0 n j l-physicalCasimir n j l ⟨t,by omega⟩-
                (recurrenceDiagonalQ n n (2*j) (2*l) (channelLabel n j l t) : ℝ) := by
          have raw_diagonal_complement (s j l k : ℚ) (hk : k≠0) (hk1 : k+1≠0) :
              rawDiagonal s l s j k+rawDiagonal s s j l k+spinCasimir k =
                2*spinCasimir s+spinCasimir j+spinCasimir l := by
            unfold rawDiagonal spinCasimir
            field_simp [hk,hk1]
            ring
          have ha := channel_admissible n j l t 0 hj hl hjl ht (by omega)
          by_cases h0 : channelLabel n j l t=0
          · have hjn : n=2*j := by have h := ha.2.2.1;unfold triangle at h;rw [h0] at h;omega
            have hln : n=2*l := by have h := ha.2.1;unfold triangle at h;rw [h0] at h;omega
            have hjl' : j=l := by omega
            simp only [h0,recurrenceDiagonalQ,if_pos rfl,physicalCasimir,Nat.cast_zero,zero_div,zero_mul]
            unfold physicalC0 casimir
            have hnq : (n : ℚ)=2*j := by exact_mod_cast hjn
            have hnr : (n : ℝ)=2*j := by exact_mod_cast hjn
            rw [←hjl',hnq,hnr]
            push_cast
            ring
          · have hp : (0 : ℚ)<(channelLabel n j l t : ℚ)/2 := by
              have hnat : 0<channelLabel n j l t := by omega
              have hq : (0 : ℚ)<channelLabel n j l t := by exact_mod_cast hnat
              positivity
            simp only [recurrenceDiagonalQ,if_neg h0]
            have h := raw_diagonal_complement ((n : ℚ)/2) j l ((channelLabel n j l t : ℚ)/2)
              (ne_of_gt hp) (by positivity)
            have hq : rawDiagonal ((n : ℚ)/2) l ((n : ℚ)/2) j ((channelLabel n j l t : ℚ)/2) =
                2*spinCasimir ((n : ℚ)/2)+spinCasimir j+spinCasimir l-spinCasimir ((channelLabel n j l t : ℚ)/2)-
                  rawDiagonal ((n : ℚ)/2) ((n : ℚ)/2) j l ((channelLabel n j l t : ℚ)/2) := by
              linear_combination h
            have hjq : (((2*j : ℕ) : ℚ)/2)=(j : ℚ) := by push_cast;ring
            have hlq : (((2*l : ℕ) : ℚ)/2)=(l : ℚ) := by push_cast;ring
            rw [hjq,hlq]
            have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
            unfold physicalC0 physicalCasimir casimir
            unfold spinCasimir at hr
            push_cast at hr ⊢
            convert hr using 1 <;> ring
        unfold physicalTprime finiteSixJJacobi
        congr 1
        · funext k
          exact star_diagonal_complement n j l k.val hj hl hjl (by omega)
        · funext k
          exact star_edge_equal n j l (channelLabel n j l k.val)
      rw [physicalM_jacobi,physicalTprime_jacobi n j l hj hl hjl]
      exact jacobi_parity_twist _ _ _ _
    have hd : diagonal (physicalCasimir n j l)*indexParity (channelWidth n j l) 0=
        indexParity (channelWidth n j l) 0*diagonal (physicalCasimir n j l) := by
      unfold indexParity
      rw [diagonal_mul_diagonal,diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    unfold physicalZ
    rw [Matrix.mul_smul,Matrix.smul_mul]
    congr 1
    calc
      _ = ((physicalM n j l*indexParity (channelWidth n j l) 0)*physicalV n j l)*indexParity (channelWidth n j l) 0 := by
        simp only [Matrix.mul_assoc]
      _ = ((indexParity (channelWidth n j l) 0*physicalTprime n j l)*physicalV n j l)*indexParity (channelWidth n j l) 0 := by
        rw [physicalM_parity n j l hj hl hjl]
      _ = indexParity (channelWidth n j l) 0*(physicalV n j l*(diagonal (physicalCasimir n j l)*indexParity (channelWidth n j l) 0)) := by
        rw [Matrix.mul_assoc (indexParity (channelWidth n j l) 0),physicalTprimeV n j l hj hl hjl]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hd];simp only [Matrix.mul_assoc]
  have physical_signed_endpoint (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
      physicalX n j l (Fin.last (channelWidth n j l)) (Fin.last (channelWidth n j l))=
        physicalZ n j l (Fin.last (channelWidth n j l)) (Fin.last (channelWidth n j l)) := by
    have physicalZ_entry (n j l : ℕ) (k h : Fin (channelWidth n j l+1)) :
        physicalZ n j l k h=(-1 : ℝ)^(channelBase n j l+k.val+h.val)*
          normalizedSixJ n (2*l) (channelLabel n j l h.val) n (2*j) (channelLabel n j l k.val) := by
      unfold physicalZ indexParity
      simp only [Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_mul,Matrix.mul_diagonal,Nat.zero_add]
      change (-1 : ℝ)^channelBase n j l*((-1 : ℝ)^k.val*
        normalizedSixJ n (2*l) (channelLabel n j l h.val) n (2*j) (channelLabel n j l k.val)*(-1 : ℝ)^h.val) = _
      rw [pow_add,pow_add]
      ring
    let b := Fin.last (channelWidth n j l)
    have hb : channelLabel n j l b.val=n+2*j := channel_last n j l hj hl hjl
    let f : ℕ → ℝ := fun i => (-1 : ℝ)^i*
      (((n+2*j+1 : ℕ) : ℝ)*(2*(i : ℝ)+1)*sixJ n n (2*i) (2*j) (2*l) (n+2*j)^2)
    have hz (i : ℕ) (hi : i < l-j ∨ min n (j+l) < i) : f i=0 := by
      have hnot : ¬admissible n n (2*i) (2*j) (2*l) (n+2*j) := by
        intro ha
        have h1 := ha.1
        have h4 := ha.2.2.2
        unfold triangle at h1 h4
        omega
      simp [f,sixJ,if_neg hnot]
    have hsum : (∑ i : Fin (channelWidth n j l+1),f (l-j+i.val))=
        ∑ i ∈ range (j+l+1),f i := by
      unfold channelWidth
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (l-j+i))]
      exact sum_shifted_support f (j+l) (min n (j+l)) (l-j) (by omega) (by omega) hz
    have hX : physicalX n j l b b=∑ i : Fin (channelWidth n j l+1),f (l-j+i.val) := by
      unfold physicalX indexParity
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
      apply sum_congr rfl
      intro i _
      have hsquare : physicalU n j l b i^2=
          ((n+2*j+1 : ℕ) : ℝ)*(2*((l-j+i.val : ℕ) : ℝ)+1)*
            sixJ n n (2*(l-j+i.val)) (2*j) (2*l) (n+2*j)^2 := by
        unfold physicalU
        rw [hb,mul_pow,Real.sq_sqrt (by positivity)]
        push_cast
        ring
      calc
        _ = (-1 : ℝ)^(l-j+i.val)*(physicalU n j l b i)^2 := by ring
        _ = _ := by rw [hsquare]
    have hmatch := signed_stretched_endpoint_match n j (l-j) (by omega)
    have hjd : j+(l-j)=l := by omega
    have hp : 2*j+(l-j)+1=j+l+1 := by omega
    rw [hjd,hp] at hmatch
    have hZ : physicalZ n j l b b=(-1 : ℝ)^(n+2*j)*((n+2*j+1 : ℕ) : ℝ)*
        sixJ n (2*l) (n+2*j) n (2*j) (n+2*j) := by
      rw [physicalZ_entry]
      have hs : channelBase n j l+b.val+b.val=n+2*j := by
        unfold channelLabel at hb
        omega
      rw [hs,hb]
      unfold normalizedSixJ
      rw [show (((n+2*j+1 : ℕ) : ℝ)*((n+2*j+1 : ℕ) : ℝ))=((n+2*j+1 : ℕ) : ℝ)^2 by ring,
        Real.sqrt_sq (by positivity)]
      ring
    change physicalX n j l b b=physicalZ n j l b b
    rw [hX,hsum,hZ]
    exact hmatch
  have hX := physicalMX n j l hj hl hjl
  have hZ := physicalMZ n j l hj hl hjl
  rw [physicalM_jacobi] at hX hZ
  apply symmetric_jacobi_intertwiner_unique (channelWidth n j l) _ _ _
    (physicalX n j l) (physicalZ n j l) _ hX hZ
    (physicalX_symmetric n j l) (physicalZ_symmetric n j l) (physical_signed_endpoint n j l hj hl hjl)
  intro t
  apply neg_ne_zero.mpr
  have he := physicalT_edge_positive n j l hj hl hjl t
  rw [physicalT,finiteSixJJacobi_edge] at he
  exact ne_of_gt he

end D5.S3.Quantum.Algebra.ZeitlinSixJ.Parity
