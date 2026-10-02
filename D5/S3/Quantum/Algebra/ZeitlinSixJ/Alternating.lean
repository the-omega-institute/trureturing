/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/Alternating
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/Alternating
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/

/-
alternating_moment_open:
  proof_shape: content
  escape_witness: physical_signed_addition: physicalX n j l = physicalZ n j l under j<=l<=n. Its endpoint/column-propagation construction stays live in the central diagonal of physicalT*physicalX.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.Parity

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.Alternating
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
open D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Orthogonality
open D5.S3.Quantum.Algebra.ZeitlinSixJ.SpectralInverse
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Parity

theorem alternating_moment_open (N j l : ℕ) (hN : 2 ≤ N)
    (hj : 1 ≤ j ∧ j < N) (hl : 1 ≤ l ∧ l < N) :
    (∑ i ∈ range (N-1), (-1 : ℝ)^(i+1)*casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*
      W N (i+1) j l ^ 2) =
      (-1 : ℝ)^(N+1)*(casimir j+casimir l)*Wij N l j := by
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
  have sixJ_swap_columns (a b c d e f : ℕ) :
      sixJ a b c d e f = sixJ b a c e d f := by
    have deltaSq_swap (a b c : ℕ) : deltaSq a b c = deltaSq b a c := by
      unfold deltaSq
      rw [show b+a-c=a+b-c by omega, show b+a+c=a+b+c by omega]
      ring
    have triangle_swap (a b c : ℕ) : triangle a b c ↔ triangle b a c := by
      unfold triangle
      omega
    have ha : admissible a b c d e f ↔ admissible b a c e d f := by
      unfold admissible
      rw [← triangle_swap b a c, ← triangle_swap b d f,
        ← triangle_swap e a f, ← triangle_swap e d c]
      tauto
    have hlo : lower a b c d e f = lower b a c e d f := by
      unfold lower
      rw [show b+a+c=a+b+c by omega, show e+a+f=a+e+f by omega,
        show e+d+c=d+e+c by omega, show b+d+f=d+b+f by omega]
      ac_rfl
    have hup : upper a b c d e f = upper b a c e d f := by
      unfold upper
      rw [show b+a+e+d=a+b+d+e by omega, show a+c+d+f=c+a+f+d by omega,
        show c+b+f+e=b+c+e+f by omega]
      ac_rfl
    have ht (z : ℕ) : racahTerm a b c d e f z = racahTerm b a c e d f z := by
      unfold racahTerm
      rw [show b+a+c=a+b+c by omega, show e+a+f=a+e+f by omega,
        show e+d+c=d+e+c by omega, show b+d+f=d+b+f by omega,
        show b+a+e+d=a+b+d+e by omega, show a+c+d+f=c+a+f+d by omega,
        show c+b+f+e=b+c+e+f by omega]
      congr 1
      ring
    have hr : racahSum a b c d e f = racahSum b a c e d f := by
      simp only [racahSum, ← hlo, ← hup, ← ht]
    have hd : deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c =
        deltaSq b a c*deltaSq b d f*deltaSq e a f*deltaSq e d c := by
      rw [← deltaSq_swap b a c, ← deltaSq_swap b d f,
        ← deltaSq_swap e a f, ← deltaSq_swap e d c]
      ring
    simp only [sixJ, ← ha, ← hd, ← hr]
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
  have W_swap (N i j l : ℕ) : W N i j l=W N i l j := by
    unfold W
    calc
      _ = sixJ (2*l) (2*i) (2*j) (N-1) (N-1) (N-1) := sixJ_cycle_columns _ _ _ _ _ _
      _ = _ := sixJ_swap_columns _ _ _ _ _ _
  have Wij_swap (N i j : ℕ) : Wij N i j=Wij N j i := by
    unfold Wij
    exact sixJ_flip_pair _ _ _ _ _ _
  have alternating_moment_ordered (N j l : ℕ) (hN : 2≤N)
      (hj : 1≤j ∧ j<N) (hl : 1≤l ∧ l<N) (hjl : j≤l) :
      (∑ i ∈ range (N-1),(-1 : ℝ)^(i+1)*casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) j l^2) =
        (-1 : ℝ)^(N+1)*(casimir j+casimir l)*Wij N l j := by
    have central_alternating_moment (n j l : ℕ) (hn : 1≤n)
        (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
        (∑ i ∈ range n,(-1 : ℝ)^(i+1)*casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*
          W (n+1) (i+1) j l^2) =
            (-1 : ℝ)^n*(casimir j+casimir l)*Wij (n+1) l j := by
      have central_symbol_is_W (N i j l : ℕ) :
          sixJ (N-1) (N-1) (2*i) (2*j) (2*l) (N-1) = W N i j l := by
        unfold W
        calc
          _ = sixJ (2*j) (2*l) (2*i) (N-1) (N-1) (N-1) := sixJ_flip_pair (N-1) (N-1) (2*i) (2*j) (2*l) (N-1)
          _ = sixJ (2*i) (2*j) (2*l) (N-1) (N-1) (N-1) := sixJ_cycle_columns (2*j) (2*l) (2*i) (N-1) (N-1) (N-1)
      have channel_admissible (n j l t u : ℕ) (hj : j ≤ n)
          (hl : l ≤ n) (hjl : j ≤ l) (ht : t ≤ channelWidth n j l)
          (hu : u ≤ channelWidth n j l) :
          admissible n n (2*(l-j+u)) (2*j) (2*l) (channelLabel n j l t) := by
        have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
        unfold channelWidth at ht hu
        unfold channelLabel channelBase admissible triangle
        omega
      have channel_center_label (n j l : ℕ) (hj : j ≤ n) (hl : l ≤ n)
          (hjl : j ≤ l) :
          ∃ t ≤ channelWidth n j l, channelLabel n j l t = n := by
        have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
        refine ⟨(n-channelBase n j l)/2, ?_, ?_⟩
        · unfold channelWidth channelBase
          omega
        · unfold channelLabel channelBase
          omega
      have normalizedSixJ_zero (a b u c d y : ℕ) (h : ¬admissible a b u c d y) :
          normalizedSixJ a b u c d y=0 := by
        simp only [normalizedSixJ,sixJ,if_neg h,mul_zero]
      have physicalTU (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
          physicalT n j l*physicalU n j l=physicalU n j l*
            diagonal (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val)) := by
        have channel_last (n j l : ℕ) (hj : j ≤ n) (hl : l ≤ n) (hjl : j ≤ l) :
            channelLabel n j l (channelWidth n j l) = n+2*j := by
          unfold channelLabel channelBase channelWidth
          have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
          omega
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
      have physicalMX (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
          physicalM n j l*physicalX n j l=physicalX n j l*diagonal (physicalCasimir n j l) := by
        have finiteSixJJacobi_symmetric (a b c d base m : ℕ) :
            (finiteSixJJacobi a b c d base m)ᵀ=finiteSixJJacobi a b c d base m := by
          have jacobiMatrix_symmetric (m : ℕ) (a e : Fin (m+1) → ℝ) :
              (jacobiMatrix m a e)ᵀ=jacobiMatrix m a e := by
            simp only [jacobiMatrix,Matrix.transpose_add,Matrix.diagonal_transpose,Matrix.transpose_transpose]
            abel
          exact jacobiMatrix_symmetric m _ _
        have physicalDU (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
            diagonal (physicalCasimir n j l)*physicalU n j l=physicalU n j l*physicalH n j l := by
          have admissible_flip_last (a b u c d y : ℕ) :
              admissible a b u c d y ↔ admissible a d y c b u := by
            unfold admissible
            tauto
          have physicalU_dual (n j l : ℕ) :
              (physicalU n j l)ᵀ=finiteSixJMatrix n (2*l) (2*j) n (2*(l-j))
                (channelWidth n j l) (fun k : Fin (channelWidth n j l+1) => channelLabel n j l k.val) := by
            have normalizedSixJ_dual (a b u c d y : ℕ) :
                normalizedSixJ a b u c d y=normalizedSixJ a d y c b u := by
              have sixJ_flip_last (a b u c d y : ℕ) :
                  sixJ a b u c d y=sixJ a d y c b u := by
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
      have physicalZ_entry (n j l : ℕ) (k h : Fin (channelWidth n j l+1)) :
          physicalZ n j l k h=(-1 : ℝ)^(channelBase n j l+k.val+h.val)*
            normalizedSixJ n (2*l) (channelLabel n j l h.val) n (2*j) (channelLabel n j l k.val) := by
        unfold physicalZ indexParity
        simp only [Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_mul,Matrix.mul_diagonal,Nat.zero_add]
        change (-1 : ℝ)^channelBase n j l*((-1 : ℝ)^k.val*
          normalizedSixJ n (2*l) (channelLabel n j l h.val) n (2*j) (channelLabel n j l k.val)*(-1 : ℝ)^h.val) = _
        rw [pow_add,pow_add]
        ring
      rcases channel_center_label n j l hj hl hjl with ⟨t,ht,hlabel⟩
      let k : Fin (channelWidth n j l+1) := ⟨t,by omega⟩
      have hk : channelLabel n j l k.val=n := hlabel
      have hb : channelBase n j l+2*k.val=n := hk
      let f : ℕ → ℝ := fun i => (-1 : ℝ)^i*casimir i*(2*(i : ℝ)+1)*sixJ n n (2*i) (2*j) (2*l) n^2
      have hfzero (i : ℕ) (hi : i < l-j ∨ min n (j+l) < i) : f i=0 := by
        have hnot : ¬admissible n n (2*i) (2*j) (2*l) n := by
          intro ha
          have h1 := ha.1
          have h4 := ha.2.2.2
          unfold triangle at h1 h4
          omega
        simp only [f,sixJ,if_neg hnot,zero_pow (by omega : (2 : ℕ)≠0),mul_zero]
      have hfsum : (∑ i : Fin (channelWidth n j l+1),f (l-j+i.val))=
          ∑ i ∈ range (n+1),f i := by
        unfold channelWidth
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (l-j+i))]
        apply sum_shifted_support f n (min n (j+l)) (l-j) (by omega) (by omega)
        exact hfzero
      have hsquare (i : Fin (channelWidth n j l+1)) :
          physicalU n j l k i^2=((n+1 : ℕ) : ℝ)*(2*((l-j+i.val : ℕ) : ℝ)+1)*
            sixJ n n (2*(l-j+i.val)) (2*j) (2*l) n^2 := by
        unfold physicalU
        rw [hk,mul_pow,Real.sq_sqrt (by positivity)]
        push_cast
        ring
      have hmatrix : physicalT n j l*physicalX n j l=
          (physicalU n j l*diagonal (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val))*
            indexParity (channelWidth n j l) (l-j))*(physicalU n j l)ᵀ := by
        unfold physicalX
        simp only [←Matrix.mul_assoc]
        rw [physicalTU n j l hj hl hjl]
      have hm := congrArg (fun A => A k k) hmatrix
      conv_rhs at hm => rw [Matrix.mul_apply]
      simp only [indexParity,Matrix.mul_diagonal,Matrix.transpose_apply] at hm
      have hterm (i : Fin (channelWidth n j l+1)) :
          ((physicalU n j l k i*casimir (l-j+i.val))*(-1 : ℝ)^(l-j+i.val))*physicalU n j l k i=
            ((n+1 : ℕ) : ℝ)*f (l-j+i.val) := by
        calc
          _ = (-1 : ℝ)^(l-j+i.val)*casimir (l-j+i.val)*(physicalU n j l k i)^2 := by ring
          _ = _ := by rw [hsquare]; unfold f; ring
      simp_rw [hterm] at hm
      rw [←Finset.mul_sum,hfsum] at hm
      have hf0 : f 0=0 := by simp [f,casimir]
      rw [sum_range_succ',hf0,add_zero] at hm
      have hW (i : ℕ) : sixJ n n (2*i) (2*j) (2*l) n=W (n+1) i j l := by
        simpa only [Nat.add_sub_cancel_right] using central_symbol_is_W (n+1) i j l
      dsimp [f] at hm
      simp_rw [hW] at hm
      have hx := congrArg (fun A => A k k) (physical_signed_addition n j l hj hl hjl)
      rw [physicalZ_entry] at hx
      have hphase : channelBase n j l+k.val+k.val=n := by omega
      rw [hphase,hk] at hx
      unfold normalizedSixJ at hx
      rw [show (((n+1 : ℕ) : ℝ)*((n+1 : ℕ) : ℝ))=((n+1 : ℕ) : ℝ)^2 by ring,
        Real.sqrt_sq (by positivity)] at hx
      have hWij : sixJ n (2*l) n n (2*j) n=Wij (n+1) l j := by
        unfold Wij
        simp only [Nat.add_sub_cancel_right]
        exact sixJ_swap_columns n (2*l) n n (2*j) n
      rw [hWij] at hx
      have hMX := congrArg (fun A => A k k) (physicalMX n j l hj hl hjl)
      unfold physicalM at hMX
      rw [Matrix.sub_mul,Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul] at hMX
      simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_mul,Matrix.mul_diagonal] at hMX
      have hdval : physicalCasimir n j l k=((n : ℝ)/2)*((n : ℝ)/2+1) := by
        unfold physicalCasimir
        rw [hk]
        push_cast
        ring
      rw [hdval] at hMX
      have hdiag : (physicalT n j l*physicalX n j l) k k=(casimir j+casimir l)*physicalX n j l k k := by
        unfold physicalC0 at hMX
        linear_combination -hMX
      rw [hdiag,hx] at hm
      have hnp : ((n+1 : ℕ) : ℝ)≠0 := by positivity
      apply mul_left_cancel₀ hnp
      linear_combination -hm
    let n := N-1
    have hn : 1≤n := by dsimp [n];omega
    have hjn : j≤n := by dsimp [n];omega
    have hln : l≤n := by dsimp [n];omega
    have hdimN : n+1=N := by dsimp [n];omega
    have h := central_alternating_moment n j l hn hjn hln hjl
    rw [hdimN] at h
    have hs : (-1 : ℝ)^(N+1)=(-1 : ℝ)^n := by
      rw [show N+1=n+2 by omega,pow_add,neg_one_sq,mul_one]
    rw [hs]
    exact h
  by_cases horder : j≤l
  · exact alternating_moment_ordered N j l hN hj hl horder
  · have h := alternating_moment_ordered N l j hN hl hj (by omega)
    have he : (∑ i ∈ range (N-1),(-1 : ℝ)^(i+1)*casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) l j^2) =
        ∑ i ∈ range (N-1),(-1 : ℝ)^(i+1)*casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) j l^2 := by
      apply sum_congr rfl
      intro i _
      rw [W_swap N (i+1) l j]
    rw [he,Wij_swap N j l] at h
    convert h using 1 <;> ring

end D5.S3.Quantum.Algebra.ZeitlinSixJ.Alternating
