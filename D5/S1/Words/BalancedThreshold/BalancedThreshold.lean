/- GID: D5/S1/Words/BalancedThreshold/BalancedThreshold
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThreshold
   mirror-E: none(waiver:odd-balanced-threshold-resolution)
   anchors: []
   utility: none
   digest: Every odd alphabet of size at least thirteen attains the balanced threshold. -/
import D5.S1.Words.BalancedThreshold.BalancedThresholdDisplacements
import D5.S1.Words.BalancedThreshold.BalancedThresholdStrip
import D5.S1.Words.BalancedThreshold.BalancedThresholdRealization
import D5.S1.Words.BalancedThreshold.BalancedThresholdBracketing
import D5.S1.Words.BalancedThreshold.BalancedThresholdIndexing
import D5.S1.Words.BalancedThreshold.BalancedThresholdErrors
import D5.S1.Words.BalancedThreshold.BalancedThresholdSynchronization
import D5.S1.Words.BalancedThreshold.BalancedThresholdResidues
import D5.S1.Words.BalancedThreshold.BalancedThresholdLengths
import D5.S1.Words.BalancedThreshold.BalancedThresholdSlope
import D5.S1.Words.BalancedThreshold.BalancedThresholdBispecial
import D5.S1.Words.Mechanical.MechanicalPeriodicity
set_option autoImplicit false set_option relaxedAutoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 4000000
namespace D5.S1.Words.BalancedThreshold
open D5.S1.Words.Mechanical D5.S1.Words.Complexity
open BalancedThresholdDefs open scoped ENNReal
theorem result:BalancedThresholdDefs.claim:=by {
 classical {
 intro d hd hodd; obtain ⟨t, ht, rfl⟩:∃ t:ℕ, 5≤ t∧d=2*t+3:=(by
 {rcases hodd with ⟨k, hk⟩; exact (⟨k-1, by {omega}, by {omega} ⟩)}); let alpha:=(uniformSlope t);
 let u:=(lowerMechanicalWord alpha alpha); let x:=(colouredMechanicalWord alpha alpha t (by
 {omega}:0< t)); have params:(Irrational (quadraticTail t)∧((t:ℝ)-2)*quadraticTail
 t^2+((t:ℝ)-2)*((t:ℝ)+1)*quadraticTail t-((t:ℝ)+1)=0∧1/((t:ℝ)-1)< quadraticTail t∧quadraticTail
 t<1/((t:ℝ)-2)∧2<(2*(t:ℝ)-1)*quadraticTail t∧(2*(t:ℝ)+1)*quadraticTail t< t∧Irrational (uniformSlope
 t)∧1/((t:ℝ)+4)< uniformSlope t∧uniformSlope t<1/((t:ℝ)+3)):=by {
 let N:=((t-2)*(t+1)); have hN:(18≤ N):=(by {dsimp [N]; nlinarith [show 3≤ t-2 by omega]}); have
 hns:(¬ IsSquare (N*(N+4))):=(by {
 have hl:((N+1)*(N+1)< N*(N+4)):=(by {nlinarith}); have hu:(N*(N+4)<(N+1+1)*(N+1+1)):=(by
 {nlinarith}); rintro ⟨k, hk⟩; exact Nat.not_exists_sq hl hu ⟨k, hk.symm⟩}); have
 hsirr:=(irrational_sqrt_natCast_iff.mpr hns); have hirr:(Irrational (quadraticTail t)):=(by {
 change Irrational ((Real.sqrt (N*(N+4):ℕ)-N)/(2*(t-2:ℕ))); simpa only [Nat.cast_mul,
 Nat.cast_ofNat] using (hsirr.sub_natCast N).div_natCast (by omega:2*(t-2) ≠ 0)}); have htR:((5:ℝ)≤
 t):=(by {exact_mod_cast ht}); have hA:((0:ℝ)<(t:ℝ)-2):=(by {linarith}); have
 hB:((0:ℝ)<(t:ℝ)+1):=(by {linarith}); have hcast:((N:ℝ)=((t:ℝ)-2)*((t:ℝ)+1)):=(by
 {dsimp [N]; rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add]; norm_num}); let s:=(Real.sqrt
 (N*(N+4):ℕ)); let x:=(quadraticTail t); have hs:(s^2=(N:ℝ)*((N:ℝ)+4)):=(by
 {simpa [s] using Real.sq_sqrt (Nat.cast_nonneg (N*(N+4)))}); have hs0:(0≤ s):=(Real.sqrt_nonneg _);
 have hN0:((0:ℝ)< N):=(by {exact_mod_cast (by omega:0< N)}); have hNs:((N:ℝ)< s):=(by {nlinarith});
 have hxformula:(x=(s-N)/(2*((t:ℝ)-2))):=(by
 {change (s-(N:ℝ))/(2*(t-2:ℕ))=_; rw [Nat.cast_sub (by omega)]; norm_num}); have hxpos:(0< x):=(by
 {rw [hxformula]; positivity}); have hxe:(2*((t:ℝ)-2)*x=s-N):=(by {rw [hxformula]; field_simp});
 have hpoly:(((t:ℝ)-2)*x^2+((t:ℝ)-2)*((t:ℝ)+1)*x-((t:ℝ)+1)=0):=(by
 {have he:=(congrArg (fun z:ℝ=> z^2) hxe); rw [hcast] at hs he; nlinarith}); have
 hupper:(x<1/((t:ℝ)-2)):=(by {
 rw [lt_div_iff₀ hA]; by_contra hn; have hax:(1≤((t:ℝ)-2)*x):=(by {nlinarith}); have
 hbx:((t:ℝ)+1≤((t:ℝ)+1)*(((t:ℝ)-2)*x)):=(le_mul_of_one_le_right hB.le hax);
 nlinarith [mul_pos hA (sq_pos_of_pos hxpos)]}); have hlower:(1/((t:ℝ)-1)< x):=(by {
 rw [div_lt_iff₀ (by linarith:(0:ℝ)<(t:ℝ)-1)]; by_contra hn; have hxle:(x≤1):=(by {
 have ht3:((3:ℝ)≤(t:ℝ)-2):=(by {linarith}); have:=((lt_div_iff₀ hA).mp hupper); nlinarith}); have
 hsq:(x^2≤ x):=(by {nlinarith}); have hAx:(((t:ℝ)-2)*x^2≤((t:ℝ)-2)*x):=(mul_le_mul_of_nonneg_left
 hsq hA.le); have hsum:(((t:ℝ)-2)*x+((t:ℝ)-2)*((t:ℝ)+1)*x<(t:ℝ)+1):=(by {nlinarith}); linarith});
 have hsep1:(2<(2*(t:ℝ)-1)*x):=(by
 {have:=((div_lt_iff₀ (by linarith:(0:ℝ)<(t:ℝ)-1)).mp hlower); nlinarith}); have
 hmargin:((2*(t:ℝ)+1)<(t:ℝ)*((t:ℝ)-2)):=(by {nlinarith [sq_nonneg ((t:ℝ)-5)]}); have
 hsep2:((2*(t:ℝ)+1)*x< t):=(by {
 have:=((lt_div_iff₀ hA).mp hupper); have hm:=(mul_lt_mul_of_pos_right hmargin hxpos); nlinarith});
 let delta:=(1/((t:ℝ)+x)); have hd0:(0< delta):=(by {dsimp [delta]; positivity}); have
 hd1:(delta<1):=(by {dsimp [delta]; rw [div_lt_one (by positivity:(0:ℝ)<(t:ℝ)+x)]; linarith}); have
 hdi:(Irrational delta):=(by {simpa [delta, one_div] using (hirr.natCast_add t).inv}); have
 hai:(Irrational (uniformSlope t)):=(by {
 have hi:=((hdi.natCast_add (t+3)).inv); simpa [uniformSlope, delta, x, Nat.cast_add, one_div,
 add_assoc] using hi}); have hal:(1/((t:ℝ)+4)< uniformSlope t):=(by {
 change 1/((t:ℝ)+4)<1/((t:ℝ)+3+delta); exact one_div_lt_one_div_of_lt (by positivity) (by
 linarith)}); have hau:(uniformSlope t<1/((t:ℝ)+3)):=(by {
 change 1/((t:ℝ)+3+delta)<1/((t:ℝ)+3); exact one_div_lt_one_div_of_lt (by positivity) (by
 linarith)}); exact ⟨hirr, hpoly, hlower, hupper, hsep1, hsep2, hai, hal, hau⟩}; have htR:((5:ℝ)≤
 t):=(by {exact_mod_cast ht}); have hlow:(1/((t:ℝ)+4)< alpha):=(params.2.2.2.2.2.2.2.1); have
 hhigh:(alpha<1/((t:ℝ)+3)):=(params.2.2.2.2.2.2.2.2); have h0:(0< alpha):=(lt_trans (by
 {positivity}) hlow); have h13:(alpha<1/3):=(by {
 have h:=((lt_div_iff₀ (by {positivity}:(0:ℝ)<(t:ℝ)+3)).mp hhigh); nlinarith only [h, htR, h0]});
 have h1:(alpha<1):=(lt_trans h13 (by {norm_num})); have hirr:(Irrational
 alpha):=(params.2.2.2.2.2.2.1); let c:=(lowerMechanicalWindowTrueCount alpha alpha 0); let a:=(fun
 s k=> lowerMechanicalWindowTrueCount alpha alpha s k); let b:=(fun s=> s-c s); let M:=(2*t*(t+1));
 let paint:=(fun r:(ℕ)=> if r % 2=0 then 2+(r/2) % t else 2+t+(r/2) % (t+1)); have ale:(∀ s k, a s
 k≤ k):=(by {intro s k; exact ((Finset.card_filter_le _ _).trans_eq (Finset.card_range k))}); have
 telescope:(∀ s k, c (s+k)=c s+a s k):=(by {
 intro s k; simpa only [Nat.count_eq_card_filter_range, u, c, a, lowerMechanicalWindowTrueCount,
 Nat.zero_add] using Nat.count_add (fun r=> u r=true) s k}); have bwindow:(∀ s k, b (s+k)=b s+(k-a s
 k)):=(by {
 intro s k; have hcs:=(ale 0 s); have hak:=(ale s k); have hc:=(telescope s k);
 change c s≤ s at hcs; dsimp only [b]; omega}); have aone:(∀ s, a s 1=if u s=true then 1 else
 0):=(by {
 intro s; dsimp only [a, lowerMechanicalWindowTrueCount];
 simp only [Finset.range_one, Finset.filter_singleton, Nat.add_zero]; split_ifs<;> simp}); have
 ahead:(∀ s k, a s (k+1)=(if u s=true then 1 else 0)+a (s+1) k):=(by {
 intro s k; have he:=(Nat.count_add (fun r=> u (s+r)=true) 1 k); have he':(a s (k+1)=a s 1+a (s+1)
 k):=(by {
 simpa only [Nat.count_eq_card_filter_range, a, lowerMechanicalWindowTrueCount, Nat.one_add,
 Nat.add_assoc] using he}); rw [he', aone]}); have step:(∀ s, c (s+1)=c s+if u s=true then 1 else
 0):=(by {intro s; rw [telescope, aone]}); have bstep:(∀ s, b (s+1)=b s+if u s=true then 0 else
 1):=(by {
 intro s; have hs:=(step s); have hcs:=(ale 0 s); change c s≤ s at hcs; dsimp only [b];
 split_ifs at hs ⊢<;> omega}); have label:(∀ s, (x s).val=if u s=true then c s % 2 else paint (b
 s)):=(by {intro s; simp only [x, colouredMechanicalWord, u, c, b, paint]; split_ifs<;> rfl}); have
 project:(∀ s, u s=true ↔ (x s).val<2):=(by {
 intro s; rw [label]; have hm:=(Nat.mod_lt (c s) (by {omega}:0<2)); by_cases hu:u s=true; ·
 {simp [hu, hm]}; · {
 constructor; · {exact (fun h=>(hu h).elim)}; ·
 {intro hz; rw [if_neg hu] at hz; dsimp [paint] at hz; split_ifs at hz<;> omega}}}); have flabel
 (s:ℕ) (hs:u s=false):((x s).val=paint (b s)):=(by
 {simpa only [hs, Bool.false_eq_true, if_false] using label s}); have fstep (s:ℕ) (hs:u s=false):(b
 (s+1)=b s+1):=(by {simpa only [hs, Bool.false_eq_true, if_false] using bstep s}); let
 theta:=(alpha/(1-alpha)); let g:=(GenContFract.of theta); let digit:=(fun N:(ℕ)=>(if N=0 then t+2
 else if N=1 then t else if N % 2=0 then t-2 else t+1:ℕ)); let tail:=(fun N:(ℕ)=> if N=0 then
 1/((t:ℝ)+quadraticTail t) else if N % 2=1 then quadraticTail t else 1/((t:ℝ)+1+quadraticTail t));
 have even (N:ℕ) (hN:2≤ N) (heven:N % 2=0) (m U V:ℕ) (hV:V≤ t) (hnonempty:0< U+V)
 (hphase:(U:ℤ)*⌊(g).dens N⌋+(V:ℤ)*⌊(g).dens (N-1)⌋≡0 [ZMOD (t:ℤ)*((t:ℤ)+1)]):(¬
 (|2*(U:ℝ)-2*((t:ℝ)-2+1/((t:ℝ)+1+quadraticTail t))*V| <(t:ℝ)-1-m+1/((t:ℝ)+1+quadraticTail t))):=(by
 {
 let q:=(fun n=>⌊g.dens n⌋); have hstate:=(uniform_denominator_residues t ht N (by {omega})); have
 hprev:=(uniform_denominator_residues t ht (N-1) (by {omega})); have hprevodd:((N-1) % 2 ≠ 0):=(by
 {omega}); have hq:(q N≡0 [ZMOD (t:ℤ)+1]):=(by {simpa [heven] using hstate.2.2}); have hprevq:(q
 (N-1)≡1 [ZMOD (t:ℤ)+1]):=(by {simpa only [if_neg hprevodd] using hprev.2.2}); have
 hp1:=(Int.ModEq.of_dvd (dvd_mul_left ((t:ℤ)+1) (t:ℤ)) hphase); have hVp:((V:ℤ)≡0 [ZMOD
 (t:ℤ)+1]):=(by {
 have hc:=(((hq.mul_left (U:ℤ)).add (hprevq.mul_left (V:ℤ))).symm.trans hp1); simpa only [mul_zero,
 mul_one, zero_add] using hc}); have hVz:(V=0):=(by {
 have he:=(hVp.eq); have hsmall:((V:ℤ)<(t:ℤ)+1):=(by {omega}); rw [Int.emod_eq_of_lt (by
 {positivity}) hsmall, Int.zero_emod] at he; omega}); have hunit:(q N≡1 [ZMOD (t:ℤ)]∨q N≡-1 [ZMOD
 (t:ℤ)]):=(by {
 have hmod:(N % 8=0∨N % 8=2∨N % 8=4∨N % 8=6):=(by {omega}); rcases hmod with h | h | h | h; ·
 {right; simpa only [h, if_false, if_true, Nat.reduceEqDiff] using hstate.2.1}; ·
 {left; simpa only [h, if_false, if_true, Nat.reduceEqDiff] using hstate.2.1}; ·
 {left; simpa only [h, if_false, if_true, Nat.reduceEqDiff] using hstate.2.1}; ·
 {right; simpa only [h, if_false, if_true, Nat.reduceEqDiff] using hstate.2.1}}); have
 hp0:=(Int.ModEq.of_dvd (dvd_mul_right (t:ℤ) ((t:ℤ)+1)) hphase); have hUp:((U:ℤ)≡0 [ZMOD
 (t:ℤ)]):=(by {
 change (U:ℤ)*q N+(V:ℤ)*q (N-1)≡0 [ZMOD (t:ℤ)] at hp0;
 simp only [hVz, Nat.cast_zero, zero_mul, add_zero] at hp0; rcases hunit with h | h; ·
 {simpa only [mul_one] using (h.mul_left (U:ℤ)).symm.trans hp0}; · {
 have he:=(((h.mul_left (U:ℤ)).symm.trans hp0).neg); simpa only [mul_neg, mul_one, neg_neg,
 neg_zero] using he}}); have hU:(t≤ U):=(by {
 have hpos:(0< U):=(by {omega}); have he:=(hUp.eq); have hNat:(U % t=0):=(by
 {rw [← Int.natCast_emod, Int.zero_emod] at he; exact_mod_cast he}); have hdvd:(t ∣
 U):=(Nat.dvd_of_mod_eq_zero hNat); exact (Nat.le_of_dvd hpos hdvd)}); have hUR:((t:ℝ)≤ U):=(by
 {exact_mod_cast hU}); have hx:(0< quadraticTail t):=(by
 {have hp:=params; exact (lt_trans (one_div_pos.mpr (by {linarith})) hp.2.2.1)}); have
 hy1:(1/((t:ℝ)+1+quadraticTail t)<1):=(by {rw [div_lt_one (by {positivity})]; linarith});
 intro hstrip; simp only [hVz, Nat.cast_zero, mul_zero, sub_zero] at hstrip; rw [abs_of_nonneg (by
 {positivity})] at hstrip;
 linarith only [hstrip, hy1, htR, hUR, show (0:ℝ)≤ m from Nat.cast_nonneg m]}); have odd (N:ℕ)
 (hN:3≤ N) (hodd:N % 2=1) (m U V:ℕ) (hV:V≤ t) (hnonempty:0< U+V) (hphase:(U:ℤ)*⌊(g).dens
 N⌋+(V:ℤ)*⌊(g).dens (N-1)⌋≡0 [ZMOD (t:ℤ)*((t:ℤ)+1)]) (hstrip:|2*(U:ℝ)-2*((t:ℝ)+1+quadraticTail t)*V|
 <(t:ℝ)+2-m+quadraticTail t):(V=t∧U=(t+1)*t∧m< t):=(by {
 let q:=(fun n=>⌊g.dens n⌋); let x:=(quadraticTail t); have hp:=params; have hx0:(0< x):=(lt_trans
 (one_div_pos.mpr (by {linarith})) hp.2.2.1); have hsep:((t:ℝ)+2+x<2*((t:ℝ)+1)-2*(t:ℝ)*x):=(by
 {have h:=(hp.2.2.2.2.2.1); change (2*(t:ℝ)+1)*x< t at h; linarith only [h]}); have
 hstate:=(uniform_denominator_residues t ht N (by {omega})); have
 hprev:=(uniform_denominator_residues t ht (N-1) (by {omega})); have hpreveven:((N-1) % 2=0):=(by
 {omega}); have hq:(q N≡1 [ZMOD (t:ℤ)+1]):=(by {simpa [hodd] using hstate.2.2}); have hprevq:(q
 (N-1)≡0 [ZMOD (t:ℤ)+1]):=(by {simpa [hpreveven] using hprev.2.2}); have hp1:=(Int.ModEq.of_dvd
 (dvd_mul_left ((t:ℤ)+1) (t:ℤ)) hphase); have hUp:((U:ℤ)≡0 [ZMOD (t:ℤ)+1]):=(by {
 have hc:=(((hq.mul_left (U:ℤ)).add (hprevq.mul_left (V:ℤ))).symm.trans hp1); simpa only [mul_zero,
 mul_one, add_zero] using hc}); have hUdiv:(t+1 ∣ U):=(by {
 apply (Nat.dvd_of_mod_eq_zero); have he:=(hUp.eq);
 rw [← Nat.cast_add_one, ← Int.natCast_emod, Int.zero_emod] at he; exact_mod_cast he});
 obtain ⟨h, hh⟩:=(hUdiv); have hhR:((U:ℝ)=((t:ℝ)+1)*h):=(by {exact_mod_cast hh}); have hVR:((V:ℝ)≤
 t):=(by {exact_mod_cast hV}); have hxV:=(mul_le_mul_of_nonneg_left hVR hx0.le); have hVx:((0:ℝ)≤
 x*V):=(mul_nonneg hx0.le (Nat.cast_nonneg V)); have hcoeff:((0:ℝ)≤2*((t:ℝ)+1)):=(by {positivity});
 have heqh:(h=V):=(by {
 by_contra hn; rw [abs_lt] at hstrip; rcases lt_or_gt_of_ne hn with hhV | hVh; · {
 have he:((h:ℝ)+1≤ V):=(by {exact_mod_cast (by {omega}:h+1≤ V)}); have
 hm:=(mul_le_mul_of_nonneg_left he hcoeff); nlinarith only [hstrip.1, hhR, hm, hVx, hsep, hx0, hxV,
 show (0:ℝ)≤ m from Nat.cast_nonneg m]}; · {
 have he:((V:ℝ)+1≤ h):=(by {exact_mod_cast (by {omega}:V+1≤ h)}); have
 hm:=(mul_le_mul_of_nonneg_left he hcoeff); nlinarith only [hstrip.2, hhR, hm, hxV, hsep, show
 (0:ℝ)≤ m from Nat.cast_nonneg m]}}); have hUV:(U=(t+1)*V):=(by {rw [heqh] at hh; exact (hh)}); have
 hunit:(q N+q (N-1)≡1 [ZMOD (t:ℤ)]∨q N+q (N-1)≡-1 [ZMOD (t:ℤ)]):=(by {
 have hmod:(N % 8=1∨N % 8=3∨N % 8=5∨N % 8=7):=(by {omega}); have hsum:=(hstate.2.1.add hprev.2.1);
 rcases hmod with h | h | h | h; ·
 {have hprevmod:((N-1) % 8=0):=(by {omega}); left; simpa [h, hprevmod] using hsum}; ·
 {have hprevmod:((N-1) % 8=2):=(by {omega}); left; simpa [h, hprevmod] using hsum}; ·
 {have hprevmod:((N-1) % 8=4):=(by {omega}); right; simpa [h, hprevmod] using hsum}; ·
 {have hprevmod:((N-1) % 8=6):=(by {omega}); right; simpa [h, hprevmod] using hsum}}); have
 hp0:=(Int.ModEq.of_dvd (dvd_mul_right (t:ℤ) ((t:ℤ)+1)) hphase); have hreduced:((V:ℤ)*(q N+q
 (N-1))≡0 [ZMOD (t:ℤ)]):=(by {
 change (U:ℤ)*q N+(V:ℤ)*q (N-1)≡0 [ZMOD (t:ℤ)] at hp0;
 rw [hUV, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hp0; have hm:(((t:ℤ)+1)≡1 [ZMOD (t:ℤ)]):=(by
 {
 simpa only [add_zero, zero_add] using (Int.modulus_modEq_zero (n:=(t:ℤ))).add (Int.ModEq.refl 1)});
 have hc:=(((hm.mul (Int.ModEq.refl (V:ℤ))).mul (Int.ModEq.refl (q N))).add (Int.ModEq.refl ((V:ℤ)*q
 (N-1)))); have he:=(hc.symm.trans hp0); convert he using 1; ring}); have hVp:((V:ℤ)≡0 [ZMOD
 (t:ℤ)]):=(by {
 rcases hunit with h | h; · {simpa only [mul_one] using (h.mul_left (V:ℤ)).symm.trans hreduced}; · {
 have he:=(((h.mul_left (V:ℤ)).symm.trans hreduced).neg); simpa only [mul_neg, mul_one, neg_neg,
 neg_zero] using he}}); have hVt:(V=t):=(by {
 have hpos:(0< V):=(by {rw [hUV] at hnonempty; nlinarith}); have hdvd:(t ∣ V):=(by {
 apply (Nat.dvd_of_mod_eq_zero); have he:=(hVp.eq); rw [← Int.natCast_emod, Int.zero_emod] at he;
 exact_mod_cast he}); have htV:=(Nat.le_of_dvd hpos hdvd); omega}); refine (⟨hVt, by
 {rw [hUV, hVt]}, ?_⟩); by_contra hmt; have hmR:((t:ℝ)≤ m):=(by {exact_mod_cast (by {omega}:t≤ m)});
 rw [hUV, hVt] at hstrip; push_cast at hstrip; have
 he:(2*(((t:ℝ)+1)*t)-2*((t:ℝ)+1+x)*t=-(2*(t:ℝ)*x)):=(by {ring});
 change |2*(((t:ℝ)+1)*t)-2*((t:ℝ)+1+x)*t| <(t:ℝ)+2-m+x at hstrip; rw [he, abs_neg, abs_of_nonneg (by
 {positivity})] at hstrip; have hsep1:=(hp.2.2.2.2.1); change 2<(2*(t:ℝ)-1)*x at hsep1;
 linarith only [hstrip, hmR, hsep1]}); have initial (m U V:ℕ) (hV:V≤ t) (hnonempty:0< U+V)
 (hphase:((t:ℤ)+2)*U+V≡0 [ZMOD (t:ℤ)*((t:ℤ)+1)]) (hstrip:|2*(U:ℝ)-2*((t:ℝ)+quadraticTail t)*V|
 <(t:ℝ)-m+1+quadraticTail t):(V=t∧U=t*t∧m+2≤ t):=(by {
 let x:=(quadraticTail t); have hp:=params; have hx0:(0< x):=(lt_trans (one_div_pos.mpr (by
 {linarith})) hp.2.2.1); have hsep:((t:ℝ)+2+x<2*((t:ℝ)+1)-2*(t:ℝ)*x):=(by
 {have h:=(hp.2.2.2.2.2.1); change (2*(t:ℝ)+1)*x< t at h; linarith only [h]}); have
 hp1:=(Int.ModEq.of_dvd (dvd_mul_left ((t:ℤ)+1) (t:ℤ)) hphase); have hJdvd:((t:ℤ)+1 ∣
 (U:ℤ)-(t:ℤ)*V):=(by {
 have h:=(dvd_sub (Int.modEq_zero_iff_dvd.mp hp1) (dvd_mul_right ((t:ℤ)+1) ((U:ℤ)+V))); have
 he:((((t:ℤ)+2)*U+V)-(((t:ℤ)+1)*((U:ℤ)+V))=(U:ℤ)-(t:ℤ)*V):=(by {ring}); rw [he] at h; exact (h)});
 obtain ⟨h, hh⟩:=(hJdvd); have hhR:((U:ℝ)-(t:ℝ)*V=((t:ℝ)+1)*h):=(by {exact_mod_cast hh}); have
 hVR:((V:ℝ)≤ t):=(by {exact_mod_cast hV}); have hxV:=(mul_le_mul_of_nonneg_left hVR hx0.le); have
 hVx:((0:ℝ)≤ x*V):=(mul_nonneg hx0.le (Nat.cast_nonneg V)); have hcoeff:((0:ℝ)≤2*((t:ℝ)+1)):=(by
 {positivity}); have heqh:(h=0):=(by {
 by_contra hn; rw [abs_lt] at hstrip; rcases lt_or_gt_of_ne hn with hh0 | h0h; · {
 have he:((h:ℝ)≤-1):=(by {exact_mod_cast (by {omega}:h≤-1)}); have hm:=(mul_le_mul_of_nonneg_left he
 hcoeff); nlinarith only [hstrip.1, hhR, hm, hVx, hsep, hx0, hxV, show (0:ℝ)≤ m from
 Nat.cast_nonneg m]}; · {
 have he:((1:ℝ)≤ h):=(by {exact_mod_cast (by {omega}:1≤ h)}); have hm:=(mul_le_mul_of_nonneg_left he
 hcoeff); nlinarith only [hstrip.2, hhR, hm, hxV, hsep, show (0:ℝ)≤ m from Nat.cast_nonneg m]}});
 have hUV:(U=t*V):=(by {rw [heqh, mul_zero] at hh; exact_mod_cast (by {omega}:(U:ℤ)=(t:ℤ)*V)}); have
 hp0:=(Int.ModEq.of_dvd (dvd_mul_right (t:ℤ) ((t:ℤ)+1)) hphase); rw [hUV, Nat.cast_mul] at hp0; have
 hVp:((V:ℤ)≡0 [ZMOD (t:ℤ)]):=(by {
 have he:(((t:ℤ)+2)*((t:ℤ)*V)+V≡V [ZMOD (t:ℤ)]):=(by {
 rw [Int.ModEq];simp only [Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul, mul_zero,
 Int.zero_emod, zero_add, Int.emod_emod]}); exact (he.symm.trans hp0)}); have hVt:(V=t):=(by {
 have hpos:(0< V):=(by {rw [hUV] at hnonempty; nlinarith}); have hdvd:(t ∣ V):=(by {
 apply (Nat.dvd_of_mod_eq_zero); have he:=(hVp.eq); rw [← Int.natCast_emod, Int.zero_emod] at he;
 exact_mod_cast he}); have htV:=(Nat.le_of_dvd hpos hdvd); omega}); refine (⟨hVt, by
 {rw [hUV, hVt]}, ?_⟩); by_contra hmt; have hmR:((t:ℝ)-1≤ m):=(by
 {exact_mod_cast (by {omega}:(t:ℤ)-1≤ m)}); rw [hUV, hVt] at hstrip; push_cast at hstrip; have
 he:(2*((t:ℝ)*t)-2*((t:ℝ)+x)*t=-(2*(t:ℝ)*x)):=(by {ring});
 change |2*((t:ℝ)*t)-2*((t:ℝ)+x)*t| <(t:ℝ)-m+1+x at hstrip; rw [he, abs_neg, abs_of_nonneg (by
 {positivity})] at hstrip; have hsep1:=(hp.2.2.2.2.1); change 2<(2*(t:ℝ)-1)*x at hsep1;
 linarith only [hstrip, hmR, hsep1]}); have margin (a m:ℕ) (ha:a≤ t+1) (hm:m+2≤ a) (R H:ℝ) (hH:0≤ H)
 (hRH:H< R):((2*(t:ℝ)+1)*(((m:ℝ)+1)*R+H-2)<2*(a:ℝ)*t*R+2*(t:ℝ)*H):=(by {
 have haR:((a:ℝ)≤(t:ℝ)+1):=(by {exact_mod_cast ha}); have hmR:((m:ℝ)+1≤(a:ℝ)-1):=(by
 {exact_mod_cast (by {omega}:(m:ℤ)+1≤(a:ℤ)-1)}); have hmprod:=(mul_le_mul_of_nonneg_left hmR (by
 {positivity}:(0:ℝ)≤2*(t:ℝ)+1)); have hcoef:((t:ℝ)≤2*(t:ℝ)*a-(2*(t:ℝ)+1)*((m:ℝ)+1)):=(by
 {nlinarith only [hmprod, haR]}); have hR:(0< R):=(lt_of_le_of_lt hH hRH); have
 hmult:=(mul_le_mul_of_nonneg_right hcoef hR.le); have htprod:=(mul_le_mul_of_nonneg_right (by
 {linarith}:(1:ℝ)≤ t) hR.le); have hsmall:(0<(t:ℝ)*R-H+2*(2*(t:ℝ)+1)):=(by
 {nlinarith only [htprod, hRH, htR]}); have hid:(2* (a:ℝ)* t* R+ 2* (t:ℝ)* H-(2* (t:ℝ)+ 1)* (((m:ℝ)+
 1)* R+ H-2)=(2* (t:ℝ)* a-(2* (t:ℝ)+ 1)* ((m:ℝ)+ 1))* R-H+ 2* (2* (t:ℝ)+ 1)):=(by {ring});
 linarith only [hid, hmult, hsmall]}); have exclusion (N m U V n D:ℕ) (hN:1≤ N) (hUV:0< U+V):(let
 a:=(if N=1 then t else if N % 2=0 then t-2 else t+1); let z:=(if N % 2=1 then quadraticTail t else
 1/((t:ℝ)+1+quadraticTail t)); let R:=((g.contsAux (N+1)).a+(g.contsAux (N+1)).b); let
 H:=((g.contsAux N).a+(g.contsAux N).b); m<
 a→(n:ℝ)+2=((m:ℝ)+1)*R+H→(D:ℝ)=2*(U:ℝ)*R+2*(V:ℝ)*H→(U:ℤ)*⌊(g.contsAux (N+1)).b⌋+(V:ℤ)*⌊(g.contsAux
 N).b⌋≡0 [ZMOD (t:ℤ)*((t:ℤ)+1)]→|2*(U:ℝ)-2*((a:ℝ)+z)*V| <(a:ℝ)-m+1+z→(2*(t:ℝ)+1)*n< D):=(by {
 let a:=(if N=1 then t else if N % 2=0 then t-2 else t+1); let z:=(if N % 2=1 then quadraticTail t
 else 1/((t:ℝ)+1+quadraticTail t)); let R:=((g.contsAux (N+1)).a+(g.contsAux (N+1)).b); let
 H:=((g.contsAux N).a+(g.contsAux N).b); dsimp only; intro hm hn hD hp hs; change m< a at hm;
 change (n:ℝ)+2=((m:ℝ)+1)*R+H at hn; change (D:ℝ)=2*(U:ℝ)*R+2*(V:ℝ)*H at hD;
 change |2*(U:ℝ)-2*((a:ℝ)+z)*V| <(a:ℝ)-m+1+z at hs; have hH:(0<
 H):=((uniform_continuant_length_growth t ht N).1); have hRH:(H<
 R):=((uniform_continuant_length_growth t ht N).2 hN); have hR:(0< R):=(hH.trans hRH); have hx:(0<
 quadraticTail t):=(lt_trans (one_div_pos.mpr (by {linarith})) params.2.2.1); have hz:(0< z):=(by
 {dsimp [z]; split_ifs<;> positivity}); have hmR:((m:ℝ)+1≤ a):=(by {exact_mod_cast hm}); have
 hA:(1<(a:ℝ)-m+z):=(by {linarith only [hz, hmR]}); have ha:(a≤ t+1):=(by
 {dsimp [a]; split_ifs<;> omega}); have hp':((U:ℤ)*⌊g.dens N⌋+(V:ℤ)*⌊g.dens (N-1)⌋≡0 [ZMOD
 (t:ℤ)*((t:ℤ)+1)]):=(by {
 have hden:(g.dens N=(g.contsAux (N+1)).b):=(rfl); have hprev:(g.dens (N-1)=(g.contsAux N).b):=(by
 {change (g.contsAux (N-1+1)).b=_; rw [Nat.sub_add_cancel hN]}); rw [hden, hprev]; exact (hp)});
 by_cases hV:V≤ t; · {
 have hNm:((N=1∧V=t∧U=t*t∧m+2≤ t)∨(3≤ N∧N % 2=1∧V=t∧U=(t+1)*t∧m< t)):=(by {
 by_cases hN1:N=1; · {
 have hp1:(((t:ℤ)+2)*U+V≡0 [ZMOD (t:ℤ)*((t:ℤ)+1)]):=(by {
 have hq0:(g.dens 0=1):=(GenContFract.zeroth_den_eq_one); have hq1:(g.dens 1=(t:ℝ)+2):=(by
 {simpa [g] using GenContFract.first_den_eq ((uniform_ratio_expansion t ht).2 0)});
 rw [hN1, show 1-1=0 from rfl, hq0, hq1] at hp'; simpa [Int.floor_add_natCast, mul_comm] using
 hp'}); have hs1:(|2*(U:ℝ)-2*((t:ℝ)+quadraticTail t)*V| <(t:ℝ)-m+1+quadraticTail t):=(by
 {simpa only [a, z, hN1, if_pos, Nat.reduceMod, Nat.reduceEqDiff] using hs});
 obtain ⟨hVt, hUt, hmt⟩:=(initial m U V hV hUV hp1 hs1); exact (Or.inl ⟨hN1, hVt, hUt, hmt⟩)}; · {
 have hN2:(2≤ N):=(by {omega}); by_cases he:N % 2=0; · {
 have hs2:(|2*(U:ℝ)-2*((t:ℝ)-2+1/((t:ℝ)+1+quadraticTail t))*V| <(t:ℝ)-1-m+1/((t:ℝ)+1+quadraticTail
 t)):=(by {
 have ho:(N % 2 ≠ 1):=(by {omega}); have hs':=(hs); dsimp only [a, z] at hs';
 rw [if_neg hN1, if_pos he, if_neg ho, Nat.cast_sub (by {omega})] at hs';
 norm_num only [Nat.cast_ofNat] at hs'; convert hs' using 1; ring}); exact (False.elim (even N hN2
 he m U V hV hUV hp' hs2))}; · {
 have ho:(N % 2=1):=(by {omega}); have hN3:(3≤ N):=(by {omega}); have
 hs3:(|2*(U:ℝ)-2*((t:ℝ)+1+quadraticTail t)*V| <(t:ℝ)+2-m+quadraticTail t):=(by {
 dsimp only [a, z] at hs; rw [if_neg hN1, if_neg he, if_pos ho, Nat.cast_add, Nat.cast_one] at hs;
 convert hs using 1; ring}); obtain ⟨hVt, hUt, hmt⟩:=(odd N hN3 ho m U V hV hUV hp' hs3); exact
 (Or.inr ⟨hN3, ho, hVt, hUt, hmt⟩)}}}); have hma:(m+2≤ a):=(by {
 rcases hNm with ⟨hN1, _, _, hmt⟩ | ⟨hN3, ho, _, _, hmt⟩; · {simpa only [a, hN1, if_pos] using hmt};
 · {dsimp only [a]; rw [if_neg (by {omega}:¬ N=1), if_neg (by {omega}:¬ N % 2=0)]; omega}}); have
 hphysical:((D:ℝ)=2*(a:ℝ)*t*R+2*(t:ℝ)*H):=(by {
 rcases hNm with ⟨hN1, hVt, hUt, _⟩ | ⟨hN3, ho, hVt, hUt, _⟩; · {
 rw [hD, hVt, hUt]; have hcoef:(a=t):=(by {simp only [a, hN1, if_pos]}); rw [hcoef]; push_cast;
 ring}; · {
 rw [hD, hVt, hUt]; have hcoef:(a=t+1):=(by
 {simp only [a, if_neg (by {omega}:¬ N=1), if_neg (by {omega}:¬ N % 2=0)]}); rw [hcoef]; push_cast;
 ring}}); have hb:=(margin a m ha hma R H hH.le hRH); have hn':((n:ℝ)=((m:ℝ)+1)*R+H-2):=(by
 {linarith only [hn]}); rwa [← hphysical, ← hn'] at hb}; · {
 have hVt:(t+1≤ V):=(by {omega}); have hV1:((1:ℝ)≤ V):=(by {exact_mod_cast (by {omega}:1≤ V)}); have
 hUm:((m+1)*V≤ U):=(by {
 by_contra h; have hg:((U:ℝ)+1≤((m:ℝ)+1)*V):=(by {exact_mod_cast (by {omega}:U+1≤(m+1)*V)}); have
 hmul:=(mul_le_mul_of_nonneg_left hV1 (by {linarith only [hA]}:0≤(a:ℝ)-m+z-1)); have
 hlow:=((abs_lt.mp hs).1); nlinarith only [hA, hmul, hg, hlow]}); have hUmR:(((m:ℝ)+1)*V≤ U):=(by
 {exact_mod_cast hUm}); have hVbound:((t:ℝ)+1≤ V):=(by {exact_mod_cast hVt}); have
 hL:(0<((m:ℝ)+1)*R+H):=(by {positivity}); have he:((D:ℝ)-(2* (t:ℝ)+ 1)* n=2* ((U:ℝ)-((m:ℝ)+ 1)* V)*
 R+ (2* (V:ℝ)-(2* (t:ℝ)+ 1))* (((m:ℝ)+ 1)* R+ H)+ 2* (2* (t:ℝ)+ 1)):=(by
 {rw [hD]; have hn':((n:ℝ)=((m:ℝ)+1)*R+H-2):=(by {linarith only [hn]}); rw [hn']; ring}); have
 hfirst:(0≤((U:ℝ)-((m:ℝ)+1)*V)*R):=(mul_nonneg (by {linarith only [hUmR]}) hR.le); have
 hsecond:(0<(2*(V:ℝ)-(2*(t:ℝ)+1))*(((m:ℝ)+1)*R+H)):=(mul_pos (by {linarith only [hVbound]}) hL);
 nlinarith only [he, hfirst, hsecond, htR]}}); have returns (n:ℕ) (w:Fin n→Bool) (hw:BispecialFactor
 (u) w):(∃ N m:ℕ, m< digit N∧let v:=(g.contsAux (N+1)); let z:=(g.contsAux N);
 (n:ℝ)+2=((m:ℝ)+1)*(v.a+v.b)+z.a+z.b∧((List.ofFn w).count true:ℝ)+1=((m:ℝ)+1)*v.a+z.a∧(0<(List.ofFn
 w).count true→1≤ N)∧(∃ p q r s:ℕ,
 (p*s+1=r*q∨r*q+1=p*s)∧(p:ℝ)=v.a∧(q:ℝ)=v.b∧(r:ℝ)=(m:ℝ)*v.a+z.a∧(s:ℝ)=(m:ℝ)*v.b+z.b)∧∀ i j, i<
 j→wordFactor (u) n i=w→wordFactor (u) n j=w→∃ k l:ℕ, 0< k+l∧(lowerMechanicalWindowTrueCount alpha
 alpha i (j-i):ℝ)=(k:ℝ)*v.a+(l:ℝ)*((m:ℝ)*v.a+z.a)∧((j-i-lowerMechanicalWindowTrueCount alpha alpha i
 (j-i):ℕ):ℝ)=(k:ℝ)*v.b+(l:ℝ)*((m:ℝ)*v.b+z.b)∧|(l:ℝ)-(k:ℝ)/((digit N:ℝ)-m+tail N)| <1+1/((digit
 N:ℝ)-m+tail N)):=(by {
 classical {
 have hp:=params; have hhalf:(alpha<1/2):=(by {linarith}); have hai:(Irrational
 alpha):=(hp.2.2.2.2.2.2.1); have hb0:(0<1-alpha):=(by {linarith}); have htheta0:(0<
 theta):=(div_pos h0 hb0); have htheta1:(theta<1):=((div_lt_one hb0).mpr (by {linarith})); have
 hthetai:(Irrational theta):=(by {
 have he:(theta=1/(1/alpha-1)):=(by {dsimp [theta]; field_simp}); rw [he]; simpa [one_div] using
 (hai.inv.sub_ratCast 1).inv}); have total:(∀ v:(List Bool), v.count true+v.count
 false=v.length):=(by {
 intro v; have eq1:((fun b:(Bool)=> b==true)=(fun b=> b)):=(by {funext b; cases b<;> rfl}); have
 eq2:((fun b:(Bool)=> b==false)=(fun b=> decide (¬ b=true))):=(by {funext b; cases b<;> rfl}); simpa
 only [List.count, eq1, eq2] using (List.length_eq_countP_add_countP (fun b:(Bool)=> b)
 (l:=v)).symm}); have window:(∀ d i, (List.ofFn (wordFactor u d i)).count
 true=lowerMechanicalWindowTrueCount alpha alpha i d):=(by {
 intro d i; have he:(List.ofFn (wordFactor u d i)=(List.range d).map (fun k=> u (i+k))):=(by
 {rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]; rfl}); rw [he]; have
 hrange:((List.range d).toFinset=Finset.range d):=(by {ext k; simp}); have hh:=((List.nodup_range
 (n:=d)).card_eq_countP (P:=fun k=> u (i+k)=true)); rw [hrange] at hh; simpa [List.count_eq_countP,
 List.countP_map, lowerMechanicalWindowTrueCount, u, Function.comp_def, lowerMechanicalWord] using
 hh.symm}); obtain ⟨r, s, hr, hs, hd, hc, hdisp⟩:=(mechanical_return_displacements h0 h1 hai w hw);
 obtain ⟨r', s', _, _, hd', hc', hadj⟩:=(mechanical_bispecial_returns h0 h1 hai w hw); let
 A:(ℤ):=((List.ofFn w).count true+1); let B:(ℤ):=((List.ofFn w).count false+1); have hA:(0< A):=(by
 {dsimp [A]; omega}); have hB:(0< B):=(by {dsimp [B]; omega}); have uniq:(∀ p q P Q:(ℤ), 0≤ p→0≤
 q→p≤ A→q≤ B→0≤ P→0≤ Q→P≤ A→Q≤ B→p*B-q*A=1→P*B-Q*A=1→p=P∧q=Q):=(by {
 intro p q P Q hp hq hpA hqB hP hQ hPA hQB hd hD; have hp0:(0< p):=(by
 {nlinarith [mul_nonneg hq hA.le]}); have hP0:(0< P):=(by {nlinarith [mul_nonneg hQ hA.le]}); let
 z:=(p*(Q-q)-q*(P-p)); have he:(P-p=A*z):=(by {dsimp [z]; linear_combination p*hD-P*hd}); have
 hz:(z=0):=(by {
 by_contra hn; rcases lt_or_gt_of_ne hn with hz | hz; · {
 have hm:=(mul_le_mul_of_nonneg_left (by {omega}:z≤-1) hA.le); nlinarith only [he, hm, hpA, hP0]}; ·
 {
 have hm:=(mul_le_mul_of_nonneg_left (by {omega}:1≤ z) hA.le); nlinarith only [he, hm, hPA, hp0]}});
 have heP:(p=P):=(by {rw [hz, mul_zero] at he; omega}); refine (⟨heP, ?_⟩); rw [heP] at hd;
 nlinarith only [hd, hD, hA]}); have sums:(∀ v z:(List Bool), (∀ b, v.count b+z.count b=(List.ofFn
 w).count b+1)→(v.count true:ℤ)+z.count true=A∧(v.count false:ℤ)+z.count false=B):=(by
 {intro v z h; constructor<;> dsimp [A, B]<;> exact_mod_cast h _}); have pair:((r'.count
 true=r.count true∧r'.count false=r.count false)∨(r'.count true=s.count true∧r'.count false=s.count
 false)):=(by {
 have hsum:=(sums r s hc); have hsum':=(sums r' s' hc'); have hdet:((r.count true:ℤ)*s.count
 false+1=(s.count true:ℤ)*r.count false∨(s.count true:ℤ)*r.count false+1=(r.count true:ℤ)*s.count
 false):=(by {exact_mod_cast hd}); have hdet':((r'.count true:ℤ)*s'.count false+1=(s'.count
 true:ℤ)*r'.count false∨(s'.count true:ℤ)*r'.count false+1=(r'.count true:ℤ)*s'.count false):=(by
 {exact_mod_cast hd'}); rcases hdet with hd | hd<;> rcases hdet' with hd' | hd'; · {
 have he:=(uniq (s'.count true) (s'.count false) (s.count true) (s.count false) (by {positivity})
 (by {positivity}) (by {omega}) (by {omega}) (by {positivity}) (by {positivity}) (by {omega}) (by
 {omega}) (by {nlinarith only [hd', hsum'.1, hsum'.2]}) (by {nlinarith only [hd, hsum.1, hsum.2]}));
 left; constructor<;> omega}; · {
 have he:=(uniq (r'.count true) (r'.count false) (s.count true) (s.count false) (by {positivity})
 (by {positivity}) (by {omega}) (by {omega}) (by {positivity}) (by {positivity}) (by {omega}) (by
 {omega}) (by {nlinarith only [hd', hsum'.1, hsum'.2]}) (by {nlinarith only [hd, hsum.1, hsum.2]}));
 right; constructor<;> omega}; · {
 have he:=(uniq (s'.count true) (s'.count false) (r.count true) (r.count false) (by {positivity})
 (by {positivity}) (by {omega}) (by {omega}) (by {positivity}) (by {positivity}) (by {omega}) (by
 {omega}) (by {nlinarith only [hd', hsum'.1, hsum'.2]}) (by {nlinarith only [hd, hsum.1, hsum.2]}));
 right; constructor<;> omega}; · {
 have he:=(uniq (r'.count true) (r'.count false) (r.count true) (r.count false) (by {positivity})
 (by {positivity}) (by {omega}) (by {omega}) (by {positivity}) (by {positivity}) (by {omega}) (by
 {omega}) (by {nlinarith only [hd', hsum'.1, hsum'.2]}) (by {nlinarith only [hd, hsum.1, hsum.2]}));
 left; constructor<;> omega}}); have pairs:(((r'.count true=r.count true∧r'.count false=r.count
 false)∧(s'.count true=s.count true∧s'.count false=s.count false))∨((r'.count true=s.count
 true∧r'.count false=s.count false)∧(s'.count true=r.count true∧s'.count false=r.count false))):=(by
 {
 rcases pair with h | h; · {
 left; refine (⟨h, ?_⟩); have h1:=(hc true); have h2:=(hc false); have h3:=(hc' true); have h4:=(hc'
 false); constructor<;> omega}; · {
 right; refine (⟨h, ?_⟩); have h1:=(hc true); have h2:=(hc false); have h3:=(hc' true); have
 h4:=(hc' false); constructor<;> omega}}); have hne:(r' ≠ s'):=(by
 {intro he; rw [he] at hd'; omega});
 obtain ⟨a, b, hab, hnotr⟩:=(mechanical_return_variation h0 h1 hai n w (by
 {obtain ⟨i, j, hi, hj, hwi, hwj, hn⟩:=(hw.1); exact (⟨i, hwi⟩)}) r'); have hbs:(List.ofFn
 (wordFactor u (b-a) a)=s'):=((hadj a b hab).resolve_left hnotr); obtain ⟨c, d, hcd,
 hnots⟩:=(mechanical_return_variation h0 h1 hai n w ⟨a, hab.2.1⟩ s'); have hdr:(List.ofFn
 (wordFactor u (d-c) c)=r'):=((hadj c d hcd).resolve_right hnots); have actual:(∃ a b c d,
 AdjacentOccurrences u w a b∧AdjacentOccurrences u w c d∧(List.ofFn (wordFactor u (b-a) a)).count
 true=r.count true∧(List.ofFn (wordFactor u (b-a) a)).count false=r.count false∧(List.ofFn
 (wordFactor u (d-c) c)).count true=s.count true∧(List.ofFn (wordFactor u (d-c) c)).count
 false=s.count false∧List.ofFn (wordFactor u (b-a) a) ≠ List.ofFn (wordFactor u (d-c) c)):=(by {
 rcases pairs with ⟨hp, hq⟩ | ⟨hp, hq⟩; · {
 refine (⟨c, d, a, b, hcd, hab, ?_, ?_, ?_, ?_, ?_⟩); all_goals {
 simp only [hdr, hbs]; first | {exact (hp.1)} | {exact (hp.2)} | {exact (hq.1)} | {exact (hq.2)} |
 {exact (hne)}}}; · {
 refine (⟨a, b, c, d, hab, hcd, ?_, ?_, ?_, ?_, ?_⟩); all_goals {
 simp only [hdr, hbs]; first | {exact (hp.1)} | {exact (hp.2)} | {exact (hq.1)} | {exact (hq.2)} |
 {exact (hne.symm)}}}}); obtain ⟨a, b, c, d, hab, hcd, har, haq, hcs, hcv, hdistinct⟩:=(actual);
 have lengths:(b-a=r.length∧d-c=s.length):=(by {
 have he:=(total (List.ofFn (wordFactor u (b-a) a))); have hf:=(total (List.ofFn (wordFactor u (d-c)
 c))); rw [har,haq,total r, List.length_ofFn] at he; rw [hcs, hcv, total s, List.length_ofFn] at hf;
 exact (⟨he.symm, hf.symm⟩)}); have hbr:(((r.count true:ℝ)-theta*r.count false)*((s.count
 true:ℝ)-theta*s.count false)<0):=(by {
 have he:=(mechanical_return_bracketing h0 h1 hai w hw a b c d hab hcd hdistinct);
 rw [← window, ← window, har, hcs, lengths.1, lengths.2] at he; have hscale:(∀ v:(List Bool),
 (v.count true:ℝ)-alpha*v.length=(1-alpha)*((v.count true:ℝ)-theta*v.count false)):=(by
 {intro v; rw [← total v]; dsimp [theta]; push_cast; field_simp; ring}); rw [hscale, hscale] at he;
 nlinarith only [he, sq_pos_of_pos hb0]}); obtain ⟨N, m, digitI, hget, hmI,
 hindex⟩:=(unimodular_bracket_continuants htheta0 htheta1 hthetai (r.count true) (r.count false)
 (s.count true) (s.count false) hd hbr); have hdigit:((digitI:ℝ)=(digit N:ℝ)):=(by {
 have hs:=((uniform_ratio_expansion t ht).2 N); rw [hs] at hget; exact (congrArg (fun
 v:(GenContFract.Pair ℝ)=> v.b) (Option.some.inj hget).symm)}); have hm:(m< digit N):=(by {
 have hmR:((m:ℝ)< digitI):=(by {exact_mod_cast hmI}); exact_mod_cast (hmR.trans_eq hdigit)}); let
 v:=(g.contsAux (N+1)); let z:=(g.contsAux N); have
 hgeometry:((n:ℝ)+2=((m:ℝ)+1)*(v.a+v.b)+z.a+z.b∧((List.ofFn w).count
 true:ℝ)+1=((m:ℝ)+1)*v.a+z.a):=(by {
 have hcT:((r.count true:ℝ)+s.count true=(List.ofFn w).count true+1):=(by {exact_mod_cast hc true});
 have hcF:((r.count false:ℝ)+s.count false=(List.ofFn w).count false+1):=(by
 {exact_mod_cast hc false}); have hwtotal:(((List.ofFn w).count true:ℝ)+(List.ofFn w).count
 false=n):=(by {exact_mod_cast (total (List.ofFn w)).trans (List.length_ofFn (f:=w))});
 rcases hindex with ⟨hv, hz⟩ | ⟨hv, hz⟩; all_goals {
 have hpa:=(congrArg GenContFract.Pair.a hv); have hpb:=(congrArg GenContFract.Pair.b hv); have
 hqa:=(congrArg GenContFract.Pair.a hz); have hqb:=(congrArg GenContFract.Pair.b hz);
 change _=v.a at hpa; change _=v.b at hpb; change _=(m:ℝ)*v.a+z.a at hqa;
 change _=(m:ℝ)*v.b+z.b at hqb; constructor<;> nlinarith only [hcT, hcF, hwtotal, hpa, hpb, hqa,
 hqb]}}); let error:=(fun v:(List Bool)=>(v.count true:ℝ)-theta*v.count false); have scale:(∀
 v:(List Bool), (v.count true:ℝ)-alpha*v.length=(1-alpha)*error v):=(by
 {intro v; rw [← total v]; dsimp [error, theta]; push_cast; field_simp; ring}); have normalized:(∀ i
 j, i< j→wordFactor u n i=w→wordFactor u n j=w→|error (List.ofFn (wordFactor u (j-i) i))| <
 |error r| + |error s|):=(by {
 intro i j hij hi hj; have hstrip:=(mechanical_bispecial_strip h0 h1 hai w hw i j a b c d hij hi hj
 hab hcd hdistinct); rw [← window, ← window, ← window, har, hcs, lengths.1, lengths.2] at hstrip;
 have hiscale:=(scale (List.ofFn (wordFactor u (j-i) i))); simp only [List.length_ofFn] at hiscale;
 rw [hiscale] at hstrip; have hrscale:=(scale r); have hsscale:=(scale s);
 rw [hrscale, hsscale, abs_mul, abs_mul, abs_mul, abs_of_pos hb0] at hstrip;
 rw [← mul_add] at hstrip; exact ((mul_lt_mul_iff_right₀ hb0).mp hstrip)}); let e:=(v.a-theta*v.b);
 let A:=((digit N:ℝ)-m+tail N); have hedata:=(uniform_continuant_errors t ht N); have he0:(e ≠
 0):=(hedata.2.2.1); have ht0:(0< tail N):=(hedata.1); have hA0:(0< A):=(by
 {have hmR:((m:ℝ)< digit N):=(by {exact_mod_cast hm}); dsimp [A]; linarith}); have
 hpred:(z.a-theta*z.b=-((digit N:ℝ)+tail N)*e):=(hedata.2.2.2); have
 hsemi:((m:ℝ)*v.a+z.a-theta*((m:ℝ)*v.b+z.b)=-A*e):=(by {dsimp [A, e]; nlinarith only [hpred]}); have
 errorsum:(|error r| + |error s| =(1+A)* |e|):=(by {
 rcases hindex with ⟨hv, hz⟩ | ⟨hv, hz⟩; all_goals {
 have hpa:=(congrArg GenContFract.Pair.a hv); have hpb:=(congrArg GenContFract.Pair.b hv); have
 hqa:=(congrArg GenContFract.Pair.a hz); have hqb:=(congrArg GenContFract.Pair.b hz);
 dsimp only [GenContFract.Pair.a, GenContFract.Pair.b] at hpa hpb hqa hqb; dsimp only [error];
 rw [hpa, hpb, hqa, hqb, hsemi]; change _=(1+A)* |e|; rw [abs_mul, abs_neg, abs_of_pos hA0];
 ring}}); have initial:((g.contsAux 0).a=1∧(g.contsAux 1).a=0∧(g.contsAux 2).a=1):=(by {
 have head:(g.h=0):=((uniform_ratio_expansion t ht).1); have digits:=((uniform_ratio_expansion t
 ht).2 0); constructor; · {rfl}; constructor; · {change g.h=0; exact (head)}; · {
 rw [GenContFract.contsAux_recurrence digits rfl rfl]; change ((t+2:ℕ):ℝ)*g.h+1*1=1; rw [head];
 ring}}); have positive_index:(0<(List.ofFn w).count true→1≤ N):=(by {
 intro hpos; have hposR:((0:ℝ)<(List.ofFn w).count true):=(by {exact_mod_cast hpos}); have
 hge:=(hgeometry.2); have hN0:(N ≠ 0):=(by {
 intro hzero; change ((List.ofFn w).count true:ℝ)+1=((m:ℝ)+1)*(g.contsAux (N+1)).a+(g.contsAux N).a
 at hge; rw [hzero, Nat.zero_add, initial.2.1, initial.1] at hge; linarith only [hge, hposR]});
 omega}); have integral_pair:(∃ p q r' s':ℕ,
 (p*s'+1=r'*q∨r'*q+1=p*s')∧(p:ℝ)=v.a∧(q:ℝ)=v.b∧(r':ℝ)=(m:ℝ)*v.a+z.a∧(s':ℝ)=(m:ℝ)*v.b+z.b):=(by {
 rcases hindex with ⟨hv, hz⟩ | ⟨hv, hz⟩; · {
 refine (⟨r.count true, r.count false, s.count true, s.count false, hd, ?_⟩); exact (⟨congrArg
 GenContFract.Pair.a hv, congrArg GenContFract.Pair.b hv, congrArg GenContFract.Pair.a hz, congrArg
 GenContFract.Pair.b hz⟩)}; · {
 refine (⟨s.count true, s.count false, r.count true, r.count false, hd.symm, ?_⟩); exact (⟨congrArg
 GenContFract.Pair.a hv, congrArg GenContFract.Pair.b hv, congrArg GenContFract.Pair.a hz, congrArg
 GenContFract.Pair.b hz⟩)}}); refine (⟨N, m, hm, hgeometry.1, hgeometry.2, positive_index,
 integral_pair, ?_⟩); intro i j hij hi hj; obtain ⟨k, l, hkl, hcount, _⟩:=(hdisp i j hij hi hj);
 have hcT:((lowerMechanicalWindowTrueCount alpha alpha i (j-i):ℝ)=(k:ℝ)*r.count true+(l:ℝ)*s.count
 true):=(by {rw [← window]; exact_mod_cast hcount true}); have
 hcF:(((j-i-lowerMechanicalWindowTrueCount alpha alpha i (j-i):ℕ):ℝ)=(k:ℝ)*r.count
 false+(l:ℝ)*s.count false):=(by {
 have ht:=(total (List.ofFn (wordFactor u (j-i) i))); rw [List.length_ofFn, window] at ht; have
 hcF:(j-i-lowerMechanicalWindowTrueCount alpha alpha i (j-i)=(List.ofFn (wordFactor u (j-i)
 i)).count false):=(by {omega}); rw [hcF]; exact_mod_cast hcount false}); have hstrip:=(normalized i
 j hij hi hj); rw [errorsum] at hstrip; have hcError:(error (List.ofFn (wordFactor u (j-i)
 i))=(k:ℝ)*error r+(l:ℝ)*error s):=(by
 {dsimp [error]; rw [hcount true, hcount false]; push_cast; ring}); rw [hcError] at hstrip; have
 converted:(∀ K L:(ℕ), |((K:ℝ)-A*L)*e| <(1+A)* |e|→|(L:ℝ)-(K:ℝ)/A| <1+1/A):=(by {
 intro K L h; rw [abs_mul] at h; have hsmall:=((mul_lt_mul_iff_left₀ (abs_pos.mpr he0)).mp h); have
 heq:((L:ℝ)-(K:ℝ)/A=-((K:ℝ)-A*L)/A):=(by {field_simp; ring});
 rw [heq, abs_div, abs_neg, abs_of_pos hA0]; have hh:=((div_lt_div_iff_of_pos_right hA0).mpr
 hsmall); exact (hh.trans_eq (by {field_simp; ring}))}); rcases hindex with ⟨hv, hz⟩ | ⟨hv, hz⟩; · {
 have hpa:=(congrArg GenContFract.Pair.a hv); have hpb:=(congrArg GenContFract.Pair.b hv); have
 hqa:=(congrArg GenContFract.Pair.a hz); have hqb:=(congrArg GenContFract.Pair.b hz);
 dsimp only [GenContFract.Pair.a, GenContFract.Pair.b] at hpa hpb hqa hqb; refine (⟨k, l, hkl, ?_,
 ?_, ?_⟩); · {exact (hcT.trans (by {rw [hpa, hqa]}))}; · {exact (hcF.trans (by {rw [hpb, hqb]}))}; ·
 {
 dsimp only [error] at hstrip; rw [hpa, hpb, hqa, hqb, hsemi] at hstrip; apply (converted k l);
 exact ((by {convert hstrip using 2; ring}))}}; · {
 have hpa:=(congrArg GenContFract.Pair.a hv); have hpb:=(congrArg GenContFract.Pair.b hv); have
 hqa:=(congrArg GenContFract.Pair.a hz); have hqb:=(congrArg GenContFract.Pair.b hz);
 dsimp only [GenContFract.Pair.a, GenContFract.Pair.b] at hpa hpb hqa hqb; refine (⟨l, k, by
 {omega}, ?_, ?_, ?_⟩); · {exact (hcT.trans (by {rw [hpa, hqa]; ring}))}; ·
 {exact (hcF.trans (by {rw [hpb, hqb]; ring}))}; · {
 dsimp only [error] at hstrip; rw [hpa, hpb, hqa, hqb, hsemi] at hstrip; apply (converted l k);
 exact ((by {convert hstrip using 2; ring}))}}}}); have phase (n i j:ℕ) (hij:i≤ j) (heq:wordFactor
 (x) n i=wordFactor (x) n j) (ha:0< lowerMechanicalWindowTrueCount alpha alpha i n) (hb:2≤
 n-lowerMechanicalWindowTrueCount alpha alpha i n):(wordFactor (u) n i=wordFactor (u) n
 j∧lowerMechanicalWindowTrueCount alpha alpha i (j-i) % 2=0∧(j-i-lowerMechanicalWindowTrueCount
 alpha alpha i (j-i)) % (2*t*(t+1))=0):=(by {
 let P:=(lowerMechanicalWindowTrueCount alpha alpha i (j-i)); let Q:=(j-i-P); have
 hsync:=(palette_factor_synchronization alpha alpha t (by {omega}) n i j heq ha hb); have hci:(c i≤
 i):=((Finset.card_filter_le _ _).trans_eq (Finset.card_range i)); have hcj:(c j≤
 j):=((Finset.card_filter_le _ _).trans_eq (Finset.card_range j)); have hP:(P≤
 j-i):=((Finset.card_filter_le _ _).trans_eq (Finset.card_range _)); have htel:(c j=c i+P):=(by {
 have h:=(Nat.count_add (fun k=> u k=true) i (j-i)); simpa only [Nat.count_eq_card_filter_range,
 lowerMechanicalWindowTrueCount, Nat.zero_add, Nat.add_sub_of_le hij, c, P] using h}); have hQ:(j-c
 j=(i-c i)+Q):=(by {dsimp [Q]; omega}); refine (⟨hsync.1, ?_, ?_⟩); ·
 {change P % 2=0; have hp:=(hsync.2.1); change c i % 2=c j % 2 at hp; omega}; · {
 change Q % (2*t*(t+1))=0; have hq:=(hsync.2.2); change (i-c i) % _=(j-c j) % _ at hq;
 rw [hQ] at hq; have he:((i-c i)+Q≡(i-c i)+0 [MOD (2*t*(t+1))]):=(by
 {simpa only [Nat.ModEq, Nat.add_zero] using hq.symm}); simpa only [Nat.ModEq, Nat.zero_mod] using
 Nat.ModEq.add_left_cancel' (i-c i) he}}); have parity (p q r s k l:ℕ) (hdet:p*s+1=r*q∨r*q+1=p*s)
 (hp:(k*p+l*r) % 2=0) (hq:(k*q+l*s) % 2=0):(k % 2=0∧l % 2=0):=(by {
 have hp2:(p % 2≤1):=(by {omega}); have hq2:(q % 2≤1):=(by {omega}); have hr2:(r % 2≤1):=(by
 {omega}); have hs2:(s % 2≤1):=(by {omega}); rcases hdet with hd | hd; all_goals {
 have hm:=(congrArg (fun n:(ℕ)=> n % 2) hd); interval_cases hp0:p % 2<;> interval_cases hq0:q % 2<;>
 interval_cases hr0:r % 2<;> interval_cases hs0:s % 2; all_goals {
 simp only [Nat.add_mod, Nat.mul_mod, hp0, hq0, hr0, hs0, mul_zero, zero_mul, mul_one, one_mul,
 Nat.mod_mod] at hp hq hm; omega}}}); have transform (m a k l:ℕ) (hk:k % 2=0) (hl:l % 2=0) (q h:ℤ)
 (hphase:((k+m*l:ℕ):ℤ)*q+(l:ℤ)*h≡0 [ZMOD 2*((t:ℤ)*((t:ℤ)+1))]) (z:ℝ) (hA:0<(a:ℝ)-m+z)
 (hstrip:|(l:ℝ)-(k:ℝ)/((a:ℝ)-m+z)| <1+1/((a:ℝ)-m+z)):(∃ U V:ℕ, l=2*V∧k+m*l=2*U∧(U:ℤ)*q+(V:ℤ)*h≡0
 [ZMOD (t:ℤ)*((t:ℤ)+1)]∧|2*(U:ℝ)-2*((a:ℝ)+z)*V| <(a:ℝ)-m+1+z∧∀ R H:(ℝ),
 (k:ℝ)*R+(l:ℝ)*((m:ℝ)*R+H)=2*(U:ℝ)*R+2*(V:ℝ)*H):=(by {
 let V:=(l/2); let U:=(k/2+m*V); let A:=((a:ℝ)-m+z); have hk2:(k=2*(k/2)):=(by {omega}); have
 hl2:(l=2*V):=(by {dsimp [V]; omega}); have hU:(k+m*l=2*U):=(by
 {dsimp [U]; nlinarith only [hk2, hl2]}); have
 hphaseeq:(((k+m*l:ℕ):ℤ)*q+(l:ℤ)*h=2*((U:ℤ)*q+(V:ℤ)*h)):=(by {rw [hU, hl2]; push_cast; ring});
 rw [hphaseeq] at hphase; have hp:((U:ℤ)*q+(V:ℤ)*h≡0 [ZMOD
 (t:ℤ)*((t:ℤ)+1)]):=(Int.ModEq.mul_left_cancel' (by {norm_num}:(2:ℤ) ≠ 0) (by
 {simpa only [mul_zero] using hphase})); have hA0:(0< A):=(hA); have hAe:((1+1/A)*A=A+1):=(by
 {field_simp [hA0.ne']}); have hdist:(|(l:ℝ)*A-k| < A+1):=(by {
 have he:(((l:ℝ)-(k:ℝ)/A)*A=(l:ℝ)*A-k):=(by {field_simp [hA0.ne']}); have
 hm:=(mul_lt_mul_of_pos_right hstrip hA); change |(l:ℝ)-(k:ℝ)/A| *A<(1+1/A)*A at hm; rw [hAe] at hm;
 have hm':(|((l:ℝ)-(k:ℝ)/A)*A| < A+1):=(by {simpa only [abs_mul, abs_of_pos hA0] using hm});
 rwa [he] at hm'}); refine (⟨U, V, hl2, hU, hp, ?_, ?_⟩); · {
 have hUR:((k:ℝ)+(m:ℝ)*l=2*(U:ℝ)):=(by {exact_mod_cast hU}); have hlR:((l:ℝ)=2*(V:ℝ)):=(by
 {exact_mod_cast hl2}); have he:(2*(U:ℝ)-2*((a:ℝ)+z)*V=-((l:ℝ)*A-k)):=(by
 {dsimp [A]; linear_combination-hUR+((a:ℝ)+z)*hlR}); rw [he, abs_neg]; exact (hdist.trans_eq (by
 {dsimp [A]; ring}))}; · {
 intro R H; have hUR:((k:ℝ)+(m:ℝ)*l=2*(U:ℝ)):=(by {exact_mod_cast hU}); have
 hlR:((l:ℝ)=2*(V:ℝ)):=(by {exact_mod_cast hl2}); linear_combination R*hUR+H*hlR}}); have
 synchronized (n i j:ℕ) (hij:i< j) (heq:wordFactor (x) n i=wordFactor (x) n j) (ha:0< a i n) (hb:2≤
 n-a i n) (hw:BispecialFactor (u) (wordFactor (u) n i)):((2*(t:ℝ)+1)*n<(j-i:ℕ)):=(by {
 classical {
 let w:=(wordFactor u n i); let P:=(lowerMechanicalWindowTrueCount alpha alpha i (j-i)); let
 Q:=(j-i-P); obtain ⟨hsource, hP2, hQM⟩:=(phase n i j hij.le heq ha hb); obtain ⟨N, m, hm, hlength,
 hcount, hindexpos, hintegral, hreturns⟩:=(returns n w hw); let v:=(g.contsAux (N+1)); let
 z:=(g.contsAux N); have count_window:((List.ofFn w).count true=lowerMechanicalWindowTrueCount alpha
 alpha i n):=(by {
 have he:(List.ofFn w=(List.range n).map (fun k=> u (i+k))):=(by
 {rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]; rfl}); rw [he]; have
 hrange:((List.range n).toFinset=Finset.range n):=(by {ext k; simp}); have hh:=((List.nodup_range
 (n:=n)).card_eq_countP (P:=fun k=> u (i+k)=true)); rw [hrange] at hh; simpa [List.count_eq_countP,
 List.countP_map, lowerMechanicalWindowTrueCount, u, Function.comp_def, lowerMechanicalWord] using
 hh.symm}); have hindex:=(hindexpos (by {rwa [count_window]}));
 obtain ⟨k, l, hkl, hp, hq, hstrip⟩:=(hreturns i j hij rfl hsource.symm);
 obtain ⟨p, q, r, s, hdet, hpv, hqv, hrz, hsz⟩:=(hintegral); have hPN:(P=k*p+l*r):=(by {
 have he:((P:ℝ)=(k:ℝ)*p+(l:ℝ)*r):=(by {exact (hp.trans (by {rw [hpv, hrz]}))}); exact_mod_cast he});
 have hQN:(Q=k*q+l*s):=(by {
 have he:((Q:ℝ)=(k:ℝ)*q+(l:ℝ)*s):=(by {exact (hq.trans (by {rw [hqv, hsz]}))}); exact_mod_cast he});
 have hQ2:(Q % 2=0):=(by {
 have hd:(2 ∣ 2*t*(t+1)):=(by {use t*(t+1); ring}); exact (Nat.mod_eq_zero_of_dvd (dvd_trans hd
 (Nat.dvd_of_mod_eq_zero hQM)))}); have heven:=(parity p q r s k l hdet (by {rwa [← hPN]}) (by
 {rwa [← hQN]})); have vbi:(⌊v.b⌋=(q:ℤ)):=(by {rw [← hqv]; simp}); have
 zbi:(⌊z.b⌋=(s:ℤ)-(m:ℤ)*q):=(by {
 have he:(z.b=(((s:ℤ)-(m:ℤ)*q:ℤ):ℝ)):=(by {push_cast; rw [← hqv] at hsz; linarith only [hsz]});
 rw [he, Int.floor_intCast]}); have hphase:(((k+m*l:ℕ):ℤ)*⌊v.b⌋+(l:ℤ)*⌊z.b⌋≡0 [ZMOD
 2*((t:ℤ)*((t:ℤ)+1))]):=(by {
 have he:(((k+m*l:ℕ):ℤ)*⌊v.b⌋+(l:ℤ)*⌊z.b⌋=(Q:ℤ)):=(by {rw [vbi, zbi, hQN]; push_cast; ring});
 rw [he]; apply (Int.modEq_zero_iff_dvd.mpr); have hnat:(2*(t*(t+1)) ∣ Q):=(by
 {simpa only [Nat.mul_assoc] using Nat.dvd_of_mod_eq_zero hQM}); exact_mod_cast hnat}); have
 tailpos:(0< tail N):=((uniform_continuant_errors t ht N).1); have hA:(0<(digit N:ℝ)-m+tail N):=(by
 {have hmR:((m:ℝ)< digit N):=(by {exact_mod_cast hm}); linarith only [hmR, tailpos]}); obtain ⟨U, V,
 hl, hU, hcong, htrans, hphysical⟩:=(transform m (digit N) k l heven.1 heven.2 ⌊v.b⌋ ⌊z.b⌋ hphase
 (tail N) hA hstrip); have hUV:(0< U+V):=(by {
 by_contra h; have hu:(U=0):=(by {omega}); have hv:(V=0):=(by {omega});
 simp only [hu, hv, mul_zero] at hU hl; omega}); have hPQ:(P+Q=j-i):=(by {
 have hP:(P≤ j-i):=((Finset.card_filter_le _ _).trans_eq (Finset.card_range _)); dsimp [Q]; omega});
 have hD:(((j-i:ℕ):ℝ)=(k:ℝ)*(v.a+v.b)+(l:ℝ)*((m:ℝ)*(v.a+v.b)+(z.a+z.b))):=(by
 {have he:((P:ℝ)+Q=(j-i:ℕ)):=(by {exact_mod_cast hPQ}); nlinarith only [he, hp, hq]}); have
 hD':(((j-i:ℕ):ℝ)=2*(U:ℝ)*(v.a+v.b)+2*(V:ℝ)*(z.a+z.b)):=(hD.trans (hphysical (v.a+v.b) (z.a+z.b)));
 have hN0:(N ≠ 0):=(by {omega}); dsimp only [digit] at hm htrans; dsimp only [tail] at htrans;
 simp only [if_neg hN0] at hm htrans; apply (exclusion N m U V n (j-i) hindex hUV hm); ·
 {nlinarith only [hlength]}; · {exact (hD')}; · {exact (hcong)}; · {exact (htrans)}}}); have gap:(∀
 (i j:ℕ), i< j→u i=true→u j=true→let P:=(lowerMechanicalWindowTrueCount alpha alpha i (j-i)); 0<
 P∧P*(t+3)≤ j-i):=(by {
 intro i j hij hi hj; classical {
 let P:=(lowerMechanicalWindowTrueCount alpha alpha i (j-i)); change 0< P∧P*(t+3)≤ j-i; have hP:(0<
 P):=(by {
 apply (Finset.card_pos.mpr); refine (⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by {omega}),
 ?_⟩⟩); simpa only [Nat.add_zero] using hi}); refine (⟨hP, ?_⟩); have
 hp:=(lowerMechanicalWindowTrueCount_eq_floor (rho:=alpha) h0.le h1 i (j-i));
 rw [Nat.add_sub_of_le hij.le] at hp; have
 hpR:((P:ℝ)=(⌊alpha+(j:ℝ)*alpha⌋:ℝ)-⌊alpha+(i:ℝ)*alpha⌋):=(by {exact_mod_cast hp}); have
 hletter:=((lowerMechanicalWord_eq_true_iff alpha alpha j).mp hj);
 change ⌊alpha+((j+1:ℕ):ℝ)*alpha⌋-⌊alpha+(j:ℝ)*alpha⌋=1 at hletter; have
 hf:((⌊alpha+((j+1:ℕ):ℝ)*alpha⌋:ℝ)=(⌊alpha+(j:ℝ)*alpha⌋:ℝ)+1):=(by
 {exact_mod_cast (by {omega}:⌊alpha+((j+1:ℕ):ℝ)*alpha⌋=⌊alpha+(j:ℝ)*alpha⌋+1)}); have
 hlo:=(Int.floor_le (alpha+((j+1:ℕ):ℝ)*alpha)); have hhi:=(Int.lt_floor_add_one
 (alpha+(i:ℝ)*alpha)); rw [hf] at hlo; push_cast at hlo; have hbound:((P:ℝ)<((j:ℝ)-i+1)*alpha):=(by
 {nlinarith only [hlo, hhi, hpR]}); have hD:(((j-i:ℕ):ℝ)=(j:ℝ)-i):=(by {rw [Nat.cast_sub hij.le]});
 have ha:(alpha*((t:ℝ)+3)<1):=((lt_div_iff₀ (by {positivity}:(0:ℝ)<(t:ℝ)+3)).mp
 params.2.2.2.2.2.2.2.2); by_contra h; have hnat:(j-i+1≤ P*(t+3)):=(by {omega}); have
 hreal:(((j:ℝ)-i+1)≤(P:ℝ)*((t:ℝ)+3)):=(by
 {have hh:(((j-i:ℕ):ℝ)+1≤(P:ℝ)*((t:ℝ)+3)):=(by {exact_mod_cast hnat}); rwa [hD] at hh}); have
 hmul:=(mul_le_mul_of_nonneg_right hreal h0.le); have hstrict:=(mul_lt_mul_of_pos_left ha (by
 {exact_mod_cast hP}:(0:ℝ)< P)); nlinarith only [hmul, hstrict, hbound]}}); have paint_gap (r s:ℕ)
 (heq:paint r=paint s):(r≡s [MOD 2*t]∨r≡s [MOD 2*(t+1)]):=(by {
 have parity:(r % 2=s % 2):=(by {
 have hi':=(Nat.mod_lt (r/2) (by {omega}:0< t)); have hj':=(Nat.mod_lt (s/2) (by {omega}:0< t));
 dsimp [paint] at heq; split_ifs at heq<;> omega}); have phase_one:(r≡s [MOD 2*t]∨r≡s [MOD
 2*(t+1)]):=(by {
 by_cases hp:r % 2=0; · {
 have hp':(s % 2=0):=(by {omega}); have hf:=(heq); simp only [paint, if_pos hp, if_pos hp'] at hf;
 have half:(r/2≡s/2 [MOD t]):=(by {change _ % _=_ % _; omega}); have he:=((half.mul_left' 2).add
 (Nat.ModEq.refl (r % 2))); have hj':=(Nat.mod_add_div (s) 2); rw [← parity] at hj'; left; simpa
 only [Nat.add_comm, Nat.mod_add_div, hj'] using he}; · {
 have hp':(s % 2 ≠ 0):=(by {omega}); have hf:=(heq); simp only [paint, if_neg hp, if_neg hp'] at hf;
 have half:(r/2≡s/2 [MOD t+1]):=(by {change _ % _=_ % _; omega}); have he:=((half.mul_left' 2).add
 (Nat.ModEq.refl (r % 2))); have hj':=(Nat.mod_add_div (s) 2); rw [← parity] at hj'; right; simpa
 only [Nat.add_comm, Nat.mod_add_div, hj'] using he}}); exact (phase_one)}); have pure (n i j:ℕ)
 (hn:0< n) (hlen:n≤ t+3) (hij:i< j) (hi:∀ k, k< n→lowerMechanicalWord (uniformSlope t) alpha
 (i+k)=false) (hj:∀ k, k< n→lowerMechanicalWord (uniformSlope t) alpha (j+k)=false) (heq:wordFactor
 (colouredMechanicalWord (uniformSlope t) alpha t (by {omega})) n i=wordFactor
 (colouredMechanicalWord (uniformSlope t) alpha t (by {omega})) n j):((2*t+1)*n≤ j-i):=(by {
 classical {
 let D:=(j-i); let P:=(lowerMechanicalWindowTrueCount alpha alpha i D); let Q:=(D-P); have hP:(P<
 D):=(by {
 have hD:(0< D):=(by {dsimp [D]; omega}); have h0:(0 ∈ Finset.range D):=(Finset.mem_range.mpr hD);
 have hs:(((Finset.range D).filter (fun k=> u (i+k)=true)) ⊂ Finset.range D):=(by {
 refine (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩); intro hh; have hmem:(0 ∈
 (Finset.range D).filter (fun k=> u (i+k)=true)):=(hh.symm ▸ h0); have hu:=((Finset.mem_filter.mp
 hmem).2); have hz:(u (i+0)=false):=(hi 0 hn); simp only [Nat.add_zero] at hu hz; rw [hz] at hu;
 cases hu}); exact ((Finset.card_lt_card hs).trans_eq (Finset.card_range D))}); have hQpos:(0<
 Q):=(by {dsimp [Q]; omega}); have hb:(b j=b i+Q):=(by {
 have hc:=(telescope i D); rw [show i+D=j by {dsimp [D]; omega}] at hc; have hci:=(ale 0 i); have
 hcj:=(ale 0 j); change c i≤ i at hci; change c j≤ j at hcj; change c j=c i+P at hc;
 change j-c j=i-c i+(D-P); dsimp only [D]; omega}); have hfirst:(paint (b i)=paint (b j)):=(by {
 have he:=(congrArg Fin.val (congrFun heq ⟨0, hn⟩)); change (x (i+0)).val=(x (j+0)).val at he; simpa
 only [Nat.add_zero, flabel i (hi 0 hn), flabel j (hj 0 hn)] using he}); have phase_one:=(paint_gap
 (b i) (b j) hfirst); have parity:(b i % 2=b j % 2):=(by {
 rcases phase_one with h | h; · {exact (h.of_dvd (by {use t}))}; ·
 {exact (h.of_dvd (by {use t+1}))}}); have divisible:(∀ G, b i≡b j [MOD G]→G ∣ Q):=(by {
 intro G he; rw [hb] at he; have hh:(b i+Q≡b i+0 [MOD G]):=(by
 {simpa only [Nat.add_zero] using he.symm}); exact (Nat.dvd_of_mod_eq_zero (by
 {simpa only [Nat.ModEq, Nat.zero_mod] using hh.add_left_cancel' (b i)}))}); by_cases hn1:n=1; · {
 subst n; have hbound:(2*t≤ Q):=(by {
 rcases phase_one with he | he; · {exact (Nat.le_of_dvd hQpos (divisible _ he))}; ·
 {have hh:=(Nat.le_of_dvd hQpos (divisible _ he)); omega}}); have hD:(2*t+1≤ D):=(by {
 by_contra hnD; have hD':(D=2*t):=(by {dsimp [Q] at hbound; omega}); have hP0:(P=0):=(by
 {dsimp [Q] at hbound; omega}); have hd:=(lower_mechanical_window_true_discrepancy (rho:=alpha)
 h0.le h1 i D); change |(P:ℝ)-(D:ℝ)*alpha| <1 at hd;
 rw [hP0, hD', Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by {positivity})] at hd; have
 hlow:=((div_lt_iff₀ (by {positivity}:(0:ℝ)<(t:ℝ)+4)).mp params.2.2.2.2.2.2.2.1); push_cast at hd;
 nlinarith only [hd, hlow, h0, htR]}); simpa only [Nat.mul_one] using hD}; · {
 have hn2:(2≤ n):=(by {omega}); have hsecond:(paint (b i+1)=paint (b j+1)):=(by {
 have he:=(congrArg Fin.val (congrFun heq ⟨1, by {omega} ⟩));
 change (x (i+1)).val=(x (j+1)).val at he; rw [flabel _ (hi 1 (by {omega})), flabel _ (hj 1 (by
 {omega})), fstep i (hi 0 hn), fstep j (hj 0 hn)] at he; exact (he)}); have halves:(b i/2≡b j/2 [MOD
 t*(t+1)]):=(by {
 apply ((Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right
 t))).mp); by_cases hp:b i % 2=0; · {
 have hp':(b j % 2=0):=(by {omega}); have hnext:((b i+1) % 2 ≠ 0):=(by {omega}); have hnext':((b
 j+1) % 2 ≠ 0):=(by {omega}); simp only [paint, if_pos hp, if_pos hp'] at hfirst;
 simp only [paint, if_neg hnext, if_neg hnext', show (b i+1)/2=b i/2 by {omega}, show (b j+1)/2=b
 j/2 by {omega}] at hsecond; constructor<;> change _ % _=_ % _<;> omega}; · {
 have hp':(b j % 2 ≠ 0):=(by {omega}); have hnext:((b i+1) % 2=0):=(by {omega}); have hnext':((b
 j+1) % 2=0):=(by {omega}); simp only [paint, if_neg hp, if_neg hp'] at hfirst;
 simp only [paint, if_pos hnext, if_pos hnext', show (b i+1)/2=b i/2+1 by {omega}, show (b j+1)/2=b
 j/2+1 by {omega}] at hsecond; have hnextT:(b i/2+1≡b j/2+1 [MOD t]):=(by
 {change _ % _=_ % _; omega}); exact (⟨hnextT.add_right_cancel' 1, by {change _ % _=_ % _; omega}
 ⟩)}}); have phase:(b i≡b j [MOD M]):=(by {
 have he:=((halves.mul_left' 2).add (Nat.ModEq.refl (b i % 2))); have hj':=(Nat.mod_add_div (b j)
 2); rw [← parity] at hj'; simpa only [M, Nat.mul_assoc, Nat.add_comm, Nat.mod_add_div, hj'] using
 he}); have hMQ:(M ∣ Q):=(divisible M phase); have hQ:(M≤ Q):=(Nat.le_of_dvd hQpos hMQ); by_cases
 hnt:n≤ t; · {
 have hgoal:((2*t+1)*n≤ M):=(by {dsimp [M]; nlinarith only [hnt]}); dsimp [D, Q] at hQ; omega}; · {
 have long:(∀ (i j:ℕ), i≤ j→lowerMechanicalWindowTrueCount alpha alpha i
 (t+1)=0→lowerMechanicalWindowTrueCount alpha alpha j (t+1)=0→j-i-lowerMechanicalWindowTrueCount
 alpha alpha i (j-i)=M→False):=(by {
 intro i j hij hi hj hQ; let delta:=(1/((t:ℝ)+quadraticTail t)); let W:=(1-alpha); let
 h:=(1-((t:ℝ)+1)*alpha); let K:=(2*t-2); let P:=(lowerMechanicalWindowTrueCount alpha alpha i
 (j-i)); let f:=(fun s:(ℕ)=> alpha+(s:ℝ)*alpha-⌊alpha+(s:ℝ)*alpha⌋); have hx:(0< quadraticTail
 t):=(lt_trans (one_div_pos.mpr (by {linarith})) params.2.2.1); have hd:(0< delta):=(by
 {dsimp [delta]; positivity}); have hdt:(delta*t<1):=(by
 {dsimp [delta]; rw [one_div_mul_eq_div, div_lt_one (by {positivity})]; linarith}); have
 ha:(alpha*((t:ℝ)+3+delta)=1):=(by {dsimp [alpha, uniformSlope, delta]; field_simp}); have hW:(0<
 W):=(by {dsimp [W]; linarith}); have hK:((K:ℝ)=2*(t:ℝ)-2):=(by
 {dsimp [K]; rw [Nat.cast_sub (by {omega})]; simp}); have hM:((M:ℝ)=2*(t:ℝ)*((t:ℝ)+1)):=(by
 {dsimp [M]; push_cast; rfl}); have margin:(h<(M:ℝ)*alpha-(K:ℝ)*W∧(M:ℝ)*alpha-(K:ℝ)*W< W-h):=(by {
 have he1:(((M:ℝ)*alpha-(K:ℝ)*W-h)*((t:ℝ)+3+delta)=2-(2*(t:ℝ)-1)*delta):=(by
 {dsimp [W, h]; rw [hM, hK]; linear_combination (2*(t:ℝ)^2+5*(t:ℝ)-1)*ha}); have
 he2:((W-h-((M:ℝ)*alpha-(K:ℝ)*W))*((t:ℝ)+3+delta)=(t:ℝ)-4+(2*(t:ℝ)-2)*delta):=(by
 {dsimp [W, h]; rw [hM, hK]; linear_combination (-2*(t:ℝ)^2-3*(t:ℝ)+2)*ha}); have
 hnum1:(0<2-(2*(t:ℝ)-1)*delta):=(by {nlinarith only [hdt, hd]}); have
 hnum2:(0<(t:ℝ)-4+(2*(t:ℝ)-2)*delta):=(by
 {have hmul:=(mul_nonneg (by {linarith}:(0:ℝ)≤2*(t:ℝ)-2) hd.le); linarith only [hmul, htR]}); have
 hden:(0<(t:ℝ)+3+delta):=(by {positivity}); constructor; · {
 have hp:(0<((M:ℝ)*alpha-(K:ℝ)*W-h)):=((mul_pos_iff_of_pos_right hden).mp (he1.symm ▸ hnum1));
 linarith only [hp]}; · {
 have hp:(0< W-h-((M:ℝ)*alpha-(K:ℝ)*W)):=((mul_pos_iff_of_pos_right hden).mp (he2.symm ▸ hnum2));
 linarith only [hp]}}); have bounds:(∀ s, lowerMechanicalWindowTrueCount alpha alpha s (t+1)=0→0≤ f
 s∧f s< h):=(by {
 intro s hs; have he:=(lowerMechanicalWindowTrueCount_eq_floor (rho:=alpha) h0.le h1 s (t+1));
 rw [hs, Nat.cast_zero] at he; have heq:(⌊alpha+((s+(t+1):ℕ):ℝ)*alpha⌋=⌊alpha+(s:ℝ)*alpha⌋):=(by
 {omega}); have hlo:=(Int.floor_le (alpha+(s:ℝ)*alpha)); have hhi:=(Int.lt_floor_add_one
 (alpha+((s+(t+1):ℕ):ℝ)*alpha)); rw [heq] at hhi; push_cast at hhi; dsimp only [f, h];
 constructor<;> linarith only [hlo, hhi]}); have hfi:=(bounds i hi); have hfj:=(bounds j hj); have
 hP:(P≤ j-i):=((Finset.card_filter_le _ _).trans_eq (Finset.card_range _)); have hD:(j-i=P+M):=(by
 {change j-i-P=M at hQ; omega}); have he:=(lowerMechanicalWindowTrueCount_eq_floor (rho:=alpha)
 h0.le h1 i (j-i)); rw [Nat.add_sub_of_le hij] at he; have
 heR:((P:ℝ)=(⌊alpha+(j:ℝ)*alpha⌋:ℝ)-⌊alpha+(i:ℝ)*alpha⌋):=(by {exact_mod_cast he}); have
 hDR:((j:ℝ)-i=(P:ℝ)+M):=(by {
 have hjR:((j:ℝ)=i+((P:ℝ)+M)):=(by {exact_mod_cast (show j=i+(P+M) by {omega})});
 linarith only [hjR]}); have hdiff:(f j-f i=(M:ℝ)*alpha-(P:ℝ)*W):=(by
 {dsimp only [f, W]; linear_combination alpha*hDR+heR}); have
 hdist:(-h<(M:ℝ)*alpha-(P:ℝ)*W∧(M:ℝ)*alpha-(P:ℝ)*W< h):=(by
 {rw [← hdiff]; constructor<;> linarith only [hfi.1, hfi.2, hfj.1, hfj.2]}); by_cases hPK:P≤ K; · {
 have hpR:((P:ℝ)≤ K):=(by {exact_mod_cast hPK}); have hpW:=(mul_le_mul_of_nonneg_right hpR hW.le);
 linarith only [hpW, margin.1, hdist.2]}; · {
 have hpR:((K:ℝ)+1≤ P):=(by {exact_mod_cast (by {omega}:K+1≤ P)}); have
 hpW:=(mul_le_mul_of_nonneg_right hpR hW.le); linarith only [hpW, margin.2, hdist.1]}}); have
 zero_count:(∀ s, (∀ k, k< n→u (s+k)=false)→lowerMechanicalWindowTrueCount alpha alpha s
 (t+1)=0):=(by {
 intro s hs; apply (Finset.card_eq_zero.mpr); apply (Finset.filter_eq_empty_iff.mpr); intro k hk hu;
 have hf:=(hs k (by {have:=(Finset.mem_range.mp hk); omega})); change u (s+k)=true at hu;
 rw [hf] at hu; cases hu}); have hnot:(Q ≠ M):=(by
 {intro he; exact (long i j hij.le (zero_count i hi) (zero_count j hj) he)}); have hQ2:(2*M≤ Q):=(by
 {
 obtain ⟨k, hk⟩:=(hMQ); have hM0:(0< M):=(by {dsimp [M]; positivity}); have hk2:(2≤ k):=(by {
 by_contra hh; have hks:(k=0∨k=1):=(by {omega}); rcases hks with hk0 | hk1; ·
 {rw [hk0, mul_zero] at hk; omega}; · {rw [hk1, mul_one] at hk; exact (hnot hk)}});
 nlinarith only [hk, hk2]}); have hgoal:((2*t+1)*n≤2*M):=(by
 {dsimp [M]; have hm:=(Nat.mul_le_mul_left (2*t+1) hlen); nlinarith only [hm, ht]});
 dsimp [D, Q] at hQ2; omega}}}}); have minority (n i j e:ℕ) (hn:0< n) (hn2:n≤2) (he:e< n) (hij:i< j)
 (hi:lowerMechanicalWord (uniformSlope t) alpha (i+e)=true) (hj:lowerMechanicalWord (uniformSlope t)
 alpha (j+e)=true) (hfalse:∀ k, k< n→k ≠ e→lowerMechanicalWord (uniformSlope t) alpha
 (i+k)=false∧lowerMechanicalWord (uniformSlope t) alpha (j+k)=false) (heq:wordFactor
 (colouredMechanicalWord (uniformSlope t) alpha t (by {omega})) n i=wordFactor
 (colouredMechanicalWord (uniformSlope t) alpha t (by {omega})) n j):((2*t+1)*n≤ j-i):=(by {
 classical {
 let D:=(j-i); let P:=(lowerMechanicalWindowTrueCount alpha alpha (i+e) D); let Q:=(D-P); have
 hh:=(gap (i+e) (j+e) (by {omega}) hi hj); dsimp only at hh; rw [show (j+e)-(i+e)=D by
 {dsimp [D]; omega}] at hh; change 0< P∧P*(t+3)≤ D at hh; have hP:(0< P):=(hh.1); have hPD:(P≤
 D):=(ale _ _); have hcount:(c (j+e)=c (i+e)+P):=(by {
 have hc:=(telescope (i+e) D); rw [show i+e+D=j+e by {dsimp [D]; omega}] at hc; exact (hc)}); have
 hminor:(P % 2=0):=(by {
 have hv:=(congrArg Fin.val (congrFun heq ⟨e, he⟩)); change (x (i+e)).val=(x (j+e)).val at hv;
 rw [label, label, if_pos hi, if_pos hj, hcount] at hv; omega}); have hP2:(2≤ P):=(by {omega}); have
 hDQ:(P+Q=D):=(by {dsimp [Q]; omega}); have hQ:(P*(t+2)≤ Q):=(by {nlinarith only [hh.2, hDQ]}); have
 hQpos:(0< Q):=(by {nlinarith only [hQ, hP2]}); have hb:(b (j+e)=b (i+e)+Q):=(by {
 have hci:=(ale 0 (i+e)); have hcj:=(ale 0 (j+e)); change c (i+e)≤ i+e at hci;
 change c (j+e)≤ j+e at hcj; change j+e-c (j+e)=i+e-c (i+e)+(D-P); dsimp only [D]; omega}); by_cases
 hn1:n=1; · {
 subst n; have hgap:(2*t+1≤ D):=(by {nlinarith only [hh.2, hP2]}); simpa only [Nat.mul_one] using
 hgap}; · {
 have hn':(n=2):=(by {omega}); subst n; let f:=(1-e); have hf:(f<2):=(by {dsimp [f]; omega}); have
 hfe:(f ≠ e):=(by {dsimp [f]; omega}); obtain ⟨hif, hjf⟩:=(hfalse f hf hfe); have hmajor:(b (j+f)=b
 (i+f)+Q):=(by {
 have hecases:(e=0∨e=1):=(by {omega}); rcases hecases with he0 | he1; · {
 have hfi:(f=1):=(by {dsimp [f]; omega}); have hbi:=(bstep i); have hbj:=(bstep j);
 simp only [he0, Nat.add_zero] at hi hj hb; rw [if_pos hi] at hbi; rw [if_pos hj] at hbj; simpa only
 [hfi, hbi, hbj, Nat.add_zero] using hb}; · {
 have hfi:(f=0):=(by {dsimp [f]; omega}); have hbi:=(bstep i); have hbj:=(bstep j); have hui:(u i ≠
 true):=(by {
 simpa only [hfi, Nat.add_zero] using (show u (i+f) ≠ true from by
 {intro hh; exact (Bool.false_ne_true ((show u (i+f)=false from hif).symm.trans hh))})}); have
 huj:(u j ≠ true):=(by {
 simpa only [hfi, Nat.add_zero] using (show u (j+f) ≠ true from by
 {intro hh; exact (Bool.false_ne_true ((show u (j+f)=false from hjf).symm.trans hh))})});
 rw [if_neg hui] at hbi; rw [if_neg huj] at hbj; rw [he1, hbi, hbj] at hb; have hbeq:(b j=b
 i+Q):=(by {omega}); simpa only [hfi, Nat.add_zero] using hbeq}}); have hpaint:(paint (b
 (i+f))=paint (b (j+f))):=(by {
 have hv:=(congrArg Fin.val (congrFun heq ⟨f, hf⟩)); change (x (i+f)).val=(x (j+f)).val at hv; have
 hui:(u (i+f) ≠ true):=(by
 {intro hh; exact (Bool.false_ne_true ((show u (i+f)=false from hif).symm.trans hh))}); have huj:(u
 (j+f) ≠ true):=(by
 {intro hh; exact (Bool.false_ne_true ((show u (j+f)=false from hjf).symm.trans hh))});
 rwa [label, label, if_neg hui, if_neg huj] at hv}); have phase:(∃ G, 2*t≤ G∧G≤2*t+2∧G ∣ Q):=(by {
 have divide (G:ℕ) (hg:b (i+f)≡b (j+f) [MOD G]):(G ∣ Q):=(by {
 rw [hmajor] at hg; have he:(b (i+f)+Q≡b (i+f)+0 [MOD G]):=(by
 {simpa only [Nat.add_zero] using hg.symm}); exact (Nat.dvd_of_mod_eq_zero (by
 {simpa only [Nat.ModEq, Nat.zero_mod] using he.add_left_cancel' (b (i+f))}))});
 rcases paint_gap (b (i+f)) (b (j+f)) hpaint with h | h; ·
 {exact (⟨2*t, le_rfl, by {omega}, divide _ h⟩)}; ·
 {exact (⟨2*(t+1), by {omega}, by {omega}, divide _ h⟩)}}); obtain ⟨G, hGlo, hGhi, hGdvd⟩:=(phase);
 have hQG:(G< Q):=(by {nlinarith only [hQ, hP2, hGhi]}); have hQ2:(2*G≤ Q):=(by {
 obtain ⟨k, hk⟩:=(hGdvd); have hk2:(2≤ k):=(by {
 by_contra h; have hks:(k=0∨k=1):=(by {omega}); rcases hks with hk0 | hk1; ·
 {rw [hk0, mul_zero] at hk; omega}; · {rw [hk1, mul_one] at hk; omega}});
 nlinarith only [hk, hk2]}); change (2*t+1)*2≤ D; nlinarith only [hQ2, hP2, hGlo, hDQ]}}}); have
 short (n i j:ℕ) (hn:0< n) (hij:i< j) (heq:wordFactor (x) n i=wordFactor (x) n j) (hshort:List.ofFn
 (wordFactor (u) n i)=[true]∨List.ofFn (wordFactor (u) n i)=[true, false]∨List.ofFn (wordFactor (u)
 n i)=[false, true]∨(n≤ t+3∧List.ofFn (wordFactor (u) n i)=List.replicate n
 false)):((2*(t:ℝ)+1)*n≤(j-i:ℕ)):=(by {
 classical {
 have source:(wordFactor u n i=wordFactor u n j):=(by {
 funext r; apply (Bool.eq_iff_iff.mpr); change u (i+r)=true ↔ u (j+r)=true; rw [project, project];
 exact (Iff.of_eq (congrArg (fun z:(Fin (2*t+3))=> z.val<2) (congrFun heq r)))}); have
 resultN:((2*t+1)*n≤ j-i):=(by {
 rcases hshort with ha | hab | hba | ⟨hlen, hpure⟩; · {
 have hlen:(n=1):=(by {simpa using congrArg List.length ha}); subst n; have hui:(u i=true):=(by {
 simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, wordFactor, Nat.add_zero,
 List.cons.injEq, and_true] using ha}); have huj:(u j=true):=(by {
 have hs:=(congrFun source ⟨0, by {omega} ⟩); simpa only [wordFactor, Nat.add_zero, hui] using
 hs.symm}); exact (minority 1 i j 0 hn (by {omega}) (by {omega}) hij hui huj (by
 {intro k hk hne; omega}) heq)}; · {
 have hlen:(n=2):=(by {simpa using congrArg List.length hab}); subst n; have hui:(u i=true∧u
 (i+1)=false):=(by {
 simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, wordFactor, Nat.add_zero,
 zero_add, List.cons.injEq, and_true] using hab}); have huj:(u j=true∧u (j+1)=false):=(by {
 have hs0:=(congrFun source ⟨0, by {omega} ⟩); have hs1:=(congrFun source ⟨1, by {omega} ⟩); exact
 (⟨(by {simpa only [wordFactor, Nat.add_zero] using hs0.symm.trans hui.1}), (by
 {simpa only [wordFactor] using hs1.symm.trans hui.2})⟩)}); apply (minority 2 i j 0 hn (by {omega})
 (by {omega}) hij hui.1 huj.1 _ heq); intro k hk hne; have hk1:(k=1):=(by {omega}); simpa only [hk1]
 using And.intro hui.2 huj.2}; · {
 have hlen:(n=2):=(by {simpa using congrArg List.length hba}); subst n; have hui:(u i=false∧u
 (i+1)=true):=(by {
 simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, wordFactor, Nat.add_zero,
 zero_add, List.cons.injEq, and_true] using hba}); have huj:(u j=false∧u (j+1)=true):=(by {
 have hs0:=(congrFun source ⟨0, by {omega} ⟩); have hs1:=(congrFun source ⟨1, by {omega} ⟩); exact
 (⟨(by {simpa only [wordFactor, Nat.add_zero] using hs0.symm.trans hui.1}), (by
 {simpa only [wordFactor] using hs1.symm.trans hui.2})⟩)}); apply (minority 2 i j 1 hn (by {omega})
 (by {omega}) hij hui.2 huj.2 _ heq); intro k hk hne; have hk0:(k=0):=(by {omega}); simpa only [hk0,
 Nat.add_zero] using And.intro hui.1 huj.1}; · {
 have hi:(∀ k, k< n→u (i+k)=false):=(by {
 have hf:(wordFactor u n i=fun _=> false):=(List.ofFn_injective (by
 {simpa only [List.ofFn_const] using hpure})); intro k hk; exact (congrFun hf ⟨k, hk⟩)}); have hj:(∀
 k, k< n→u (j+k)=false):=(by {intro k hk; exact ((congrFun source ⟨k, hk⟩).symm.trans (hi k hk))});
 exact (pure n i j hn hlen hij hi hj heq)}}); exact_mod_cast resultN}}); have classify (n i:ℕ)
 (hn:0< n) (hw:BispecialFactor (x) (wordFactor (x) n i)):((0< lowerMechanicalWindowTrueCount alpha
 alpha i n∧2≤ n-lowerMechanicalWindowTrueCount alpha alpha i n∧BispecialFactor u (wordFactor u n
 i))∨(List.ofFn (wordFactor u n i)=[true]∨List.ofFn (wordFactor u n i)=[true, false]∨List.ofFn
 (wordFactor u n i)=[false, true]∨(n≤ t+3∧List.ofFn (wordFactor u n i)=List.replicate n
 false))):=(by {
 classical {
 have hlow:(1/((t:ℝ)+4)< alpha):=(params.2.2.2.2.2.2.2.1); have
 hhigh:(alpha<1/((t:ℝ)+3)):=(params.2.2.2.2.2.2.2.2); have h0:(0≤ alpha):=(le_of_lt (lt_trans (by
 {positivity}) hlow)); have h13:=(h13); have h1:=(h1); have projection:(∀ j k, wordFactor x n
 j=wordFactor x n k→wordFactor u n j=wordFactor u n k):=(by {
 intro j k he; funext r; apply (Bool.eq_iff_iff.mpr); rw [show wordFactor u n j r=u (j+r) from rfl,
 show wordFactor u n k r=u (k+r) from rfl, project, project]; exact (Iff.of_eq (congrArg (fun z:(Fin
 (2*t+3))=> z.val<2) (congrFun he r)))}); have counts:(∀ j k, wordFactor u n j=wordFactor u n k→a j
 n=a k n):=(by {
 intro j k he; dsimp [a, lowerMechanicalWindowTrueCount]; congr 1; ext r;
 simp only [Finset.mem_filter, Finset.mem_range]; constructor<;> rintro ⟨hr, hu⟩; ·
 {exact (⟨hr, by {simpa only [wordFactor] using (congrFun he ⟨r, hr⟩).symm.trans hu} ⟩)}; ·
 {exact (⟨hr, by {simpa only [wordFactor] using (congrFun he ⟨r, hr⟩).trans hu} ⟩)}}); have
 paint_congr:(∀ r s, r≡s [MOD M]→paint r=paint s):=(by {
 intro r s he; have h2:(r≡s [MOD 2]):=(he.of_dvd (by {dsimp [M]; use t*(t+1); ring})); have ht2:(r≡s
 [MOD 2*t]):=(he.of_dvd (by {dsimp [M]; use t+1})); have ht3:(r≡s [MOD 2*(t+1)]):=(he.of_dvd (by
 {dsimp [M]; use t; ring})); have hdiv:=(congrArg (fun v:(ℕ)=> v/2) ht2); have hdiv':=(congrArg (fun
 v:(ℕ)=> v/2) ht3); rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self] at hdiv hdiv';
 dsimp [paint]; rw [show r % 2=s % 2 from h2, hdiv, hdiv']}); by_cases ha:0< a i n; · {
 by_cases hb:2≤ n-a i n; · {
 left; refine (⟨ha, hb, ?_⟩); have sync:(∀ j k, wordFactor x n j=wordFactor x n i→wordFactor x n
 k=wordFactor x n i→c j≡c k [MOD 2]∧b j≡b k [MOD M]):=(by {
 intro j k hj hk; have hj':=(palette_factor_synchronization alpha alpha t (by {omega}) n i j hj.symm
 ha hb); have hk':=(palette_factor_synchronization alpha alpha t (by {omega}) n i k hk.symm ha hb);
 exact (⟨hj'.2.1.symm.trans hk'.2.1, hj'.2.2.symm.trans hk'.2.2⟩)}); have decode:(∀ j k, u j=u k→c
 j≡c k [MOD 2]→b j≡b k [MOD M]→x j=x k):=(by {
 intro j k hu hc hd; apply (Fin.ext); rw [label, label, hu]; split_ifs; · {exact (hc)}; ·
 {exact (paint_congr _ _ hd)}}); constructor; · {
 obtain ⟨j, k, hj0, hk0, hj, hk, hne⟩:=(hw.1); refine (⟨j, k, hj0, hk0, projection j i hj,
 projection k i hk, ?_⟩); intro hu; change u (j-1)=u (k-1) at hu; obtain ⟨hc, hd⟩:=(sync j k hj hk);
 have hjstep:=(step (j-1)); have hkstep:=(step (k-1)); have hjb:=(bstep (j-1)); have hkb:=(bstep
 (k-1)); rw [Nat.sub_add_cancel hj0, hu] at hjstep hjb; rw [Nat.sub_add_cancel hk0] at hkstep hkb;
 rw [hjstep, hkstep] at hc; rw [hjb, hkb] at hd; exact (hne (decode _ _ hu (hc.add_right_cancel' _)
 (hd.add_right_cancel' _)))}; · {
 obtain ⟨j, k, hj, hk, hne⟩:=(hw.2); refine (⟨j, k, projection j i hj, projection k i hk, ?_⟩);
 intro hu; obtain ⟨hc, hd⟩:=(sync j k hj hk); have hcount:=(counts j k (projection j k (hj.trans
 hk.symm))); apply (hne); apply (decode _ _ hu); ·
 {rw [telescope, telescope, hcount]; exact (hc.add_right _)}; ·
 {rw [bwindow, bwindow, hcount]; exact (hd.add_right _)}}}; · {
 right; have hdis:=((abs_lt.mp (lower_mechanical_window_true_discrepancy (rho:=alpha) h0 h1 i
 n)).2); change (a i n:ℝ)-(n:ℝ)*alpha<1 at hdis; have hmajor:(n≤ a i n+1):=(by {omega}); have
 hmajorR:((n:ℝ)≤(a i n:ℝ)+1):=(by {exact_mod_cast hmajor}); have hprod:=(mul_le_mul_of_nonneg_left
 h13.le (Nat.cast_nonneg n)); have hsmall:(n≤2):=(by {
 have hh:((n:ℝ)<3):=(by {nlinarith only [hdis, hmajorR, hprod]}); have hnlt:(n<3):=(by
 {exact_mod_cast hh}); omega}); have hlen:(n=1∨n=2):=(by {omega}); rcases hlen with hlen | hlen; · {
 subst n; left; have hc:=(aone i); have hu:(u i=true):=(by {split_ifs at hc<;> omega});
 change List.ofFn (wordFactor u 1 i)=[true]; simp only [wordFactor, List.ofFn_succ, List.ofFn_zero,
 Fin.val_zero, Nat.add_zero, hu]}; · {
 subst n; have hc:=(ahead i 1); rw [aone] at hc;
 change a i 2=(if u i=true then 1 else 0)+(if u (i+1)=true then 1 else 0) at hc; cases hui:u i<;>
 cases hui':u (i+1)<;> simp only [hui, hui', Bool.false_eq_true, if_false, if_true] at hc; ·
 {omega}; · {
 right; right; left; change List.ofFn (wordFactor u 2 i)=[false, true]; simp only [wordFactor,
 List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Nat.add_zero, zero_add, hui, hui']}; ·
 {
 right; left; change List.ofFn (wordFactor u 2 i)=[true, false]; simp only [wordFactor,
 List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Nat.add_zero, zero_add, hui, hui']}; ·
 {
 have hA:(a i 2=2):=(by {omega}); rw [hA] at hdis; norm_num only [Nat.cast_ofNat] at hdis;
 linarith only [hdis, h13]}}}}; · {
 right; right; right; right; have hz:(a i n=0):=(by {omega}); have hdis:=((abs_lt.mp
 (lower_mechanical_window_true_discrepancy (rho:=alpha) h0 h1 i n)).1);
 change-(1:ℝ)<(a i n:ℝ)-(n:ℝ)*alpha at hdis; rw [hz, Nat.cast_zero] at hdis; have hlen:(n≤ t+3):=(by
 {
 have hpos:((0:ℝ)<(t:ℝ)+4):=(by {positivity}); have hlow':=((div_lt_iff₀ hpos).mp hlow); have
 hnR:((0:ℝ)< n):=(by {exact_mod_cast hn}); have hbound:((n:ℝ)<(t:ℝ)+4):=(by
 {nlinarith only [hdis, hlow', hnR, h0]}); have hnat:(n< t+4):=(by
 {exact_mod_cast (show (n:ℝ)<(t+4:ℕ) by {simpa using hbound})}); omega}); refine (⟨hlen, ?_⟩); have
 letters:(∀ r:(Fin n), wordFactor u n i r=false):=(by {
 intro r; apply (Bool.eq_false_of_not_eq_true); intro hu; have hmem:((r:ℕ) ∈ (Finset.range n).filter
 (fun k=> u (i+k)=true)):=(by {exact (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr r.isLt, hu⟩)});
 have hempty:((Finset.range n).filter (fun k=> u (i+k)=true)=∅):=(Finset.card_eq_zero.mp hz);
 rw [hempty] at hmem; exact (Finset.notMem_empty _ hmem)});
 rw [show wordFactor u n i=fun _=> false by {funext r; exact (letters r)}]; simp}}}); refine (⟨x,
 ?_, palette_colouring_balanced h0.le h1 t (by {omega}), ?_⟩); · {
 have counts:(∀ n, Nat.count (fun k=> u k=true) n=lowerMechanicalWindowTrueCount alpha alpha 0
 n):=(by {
 intro n; simp only [Nat.count_eq_card_filter_range, lowerMechanicalWindowTrueCount, Nat.zero_add,
 u]}); have complement:(∀ n, Nat.count (fun k=> u k=false) n+Nat.count (fun k=> u k=true) n=n):=(by
 {
 intro n; simpa [Nat.count, Bool.not_eq_false] using (List.length_eq_countP_add_countP (fun k=>
 decide (u k=false)) (l:=List.range n)).symm}); have infinite:(∀ b:(Bool), (Set.ofPred (fun k=> u
 k=b)).Infinite):=(by {
 intro b hf; let K:=(hf.toFinset.card); have hb:(∀ n, Nat.count (fun k=> u k=b) n≤
 K):=(Nat.count_le_card hf); obtain ⟨n, hn⟩:=(exists_nat_gt (((K:ℝ)+1)/min alpha (1-alpha))); have
 hmin:(0< min alpha (1-alpha)):=(lt_min h0 (by {linarith})); have hn':=((div_lt_iff₀ hmin).mp hn);
 have hdis:=(abs_lt.mp (lower_mechanical_window_true_discrepancy (rho:=alpha) h0.le h1 0 n)); have
 hm1:=(mul_le_mul_of_nonneg_left (min_le_left alpha (1-alpha)) (Nat.cast_nonneg n:(0:ℝ)≤ n)); have
 hm2:=(mul_le_mul_of_nonneg_left (min_le_right alpha (1-alpha)) (Nat.cast_nonneg n:(0:ℝ)≤ n)); have
 hcount:=(hb n); cases b; · {
 have hc:=(complement n); rw [counts] at hc; have hcR:((Nat.count (fun k=> u k=false)
 n:ℝ)+lowerMechanicalWindowTrueCount alpha alpha 0 n=n):=(by {exact_mod_cast hc}); have
 hbR:((Nat.count (fun k=> u k=false) n:ℝ)≤ K):=(by {exact_mod_cast hcount});
 nlinarith only [hcR, hbR, hn', hm2, hdis.2]}; · {
 rw [counts] at hcount; have hbR:((lowerMechanicalWindowTrueCount alpha alpha 0 n:ℝ)≤ K):=(by
 {exact_mod_cast hcount}); nlinarith only [hbR, hn', hm1, hdis.1]}}); intro a; by_cases ha:a.val<2;
 · {
 let k:=(Nat.nth (fun k=> u k=true) a.val); have hk:=(Nat.nth_mem_of_infinite (infinite true)
 a.val); have hc:=(Nat.count_nth_of_infinite (infinite true) a.val); rw [counts] at hc;
 change lowerMechanicalWord alpha alpha k=true at hk;
 change lowerMechanicalWindowTrueCount alpha alpha 0 k=a.val at hc; refine (⟨k, ?_⟩); apply
 (Fin.ext); simp only [x, colouredMechanicalWord, dif_pos hk, hc, Nat.mod_eq_of_lt ha]}; · {
 let r:=(if a.val< t+2 then 2*(a.val-2) else 2*(a.val-t-2)+1); let k:=(Nat.nth (fun k=> u k=false)
 r); have hk:=(Nat.nth_mem_of_infinite (infinite false) r); have hc:=(Nat.count_nth_of_infinite
 (infinite false) r); change Nat.count (fun k=> u k=false) k=r at hc; have he:=(complement k);
 rw [counts, hc] at he; have hr:(k-lowerMechanicalWindowTrueCount alpha alpha 0 k=r):=(by {omega});
 have hkt:(lowerMechanicalWord alpha alpha k ≠ true):=(by {change u k ≠ true; rw [hk]; decide});
 refine (⟨k, ?_⟩); apply (Fin.ext); by_cases hsmall:a.val< t+2; · {
 have hpar:(r % 2=0):=(by {simp [r, hsmall]}); have hdiv:(r/2=a.val-2):=(by {simp [r, hsmall]});
 have hlt:(a.val-2< t):=(by {omega}); simp only [x, colouredMechanicalWord, dif_neg hkt, hr, dif_pos
 hpar, hdiv, Nat.mod_eq_of_lt hlt]; omega}; · {
 have hpar:(r % 2 ≠ 0):=(by {simp [r, hsmall]}); have hdiv:(r/2=a.val-t-2):=(by
 {dsimp [r]; rw [if_neg hsmall]; omega}); have hlt:(a.val-t-2< t+1):=(by {omega}); simp only [x,
 colouredMechanicalWord, dif_neg hkt, hr, dif_neg hpar, hdiv, Nat.mod_eq_of_lt hlt]; omega}}}; · {
 apply (le_antisymm); · {
 have hreturn:(∀ n (w:Fin n→Fin (2*t+3)), 0< n→BispecialFactor x w→∀ i j, AdjacentOccurrences x w i
 j→(2*(t:ℝ)+1)*n≤(j-i:ℕ)):=(by {
 intro n w hn hw i j hadj; have hwi:(w=wordFactor x n i):=(hadj.2.1.symm); subst w;
 rcases classify n i hn hw with ⟨ha, hb, hbis⟩ | hs; ·
 {exact ((synchronized n i j hadj.1 (hadj.2.1.trans hadj.2.2.1.symm) ha hb hbis).le)}; ·
 {exact (short n i j hn hadj.1 (hadj.2.1.trans hadj.2.2.1.symm) hs)}}); have
 hrec:=(coloured_word_uniformly_recurrent (rho:=alpha) h0.le h1 hirr t (by {omega})); have haper:(¬
 EventuallyPeriodicWord x):=(by {
 rintro ⟨s,p,hp,hper⟩; apply ((lower_mechanical_eventually_periodic_iff_not_irrational (rho:=alpha)
 h0.le h1).mpr ?_ hirr); refine ⟨s,p,hp,?_⟩; intro n; apply Bool.eq_iff_iff.mpr;
 rw [project,project,hper n]}); have hC:(0<2*(t:ℝ)+1):=(by {positivity}); have
 hconst:(1+1/(2*(t:ℝ)+1)=(2*(t:ℝ)+2)/(2*(t:ℝ)+1)):=(by {field_simp; ring});
 simp only [criticalExponent]; refine (iSup_le fun n=> iSup_le fun i=> iSup_le fun p=> iSup_le fun
 hp=>?_); have hbound:=(bispecial_return_period_bound x hrec haper (2*(t:ℝ)+1) hC hreturn n i p hp.1
 hp.2.2); rw [hconst] at hbound; have hpR:((0:ℝ)< p):=(by {exact_mod_cast hp.1}); have
 hr:=((div_le_iff₀ hpR).mpr hbound); have he:=(ENNReal.ofReal_le_ofReal hr);
 rw [ENNReal.ofReal_div_of_pos hpR, ENNReal.ofReal_div_of_pos hC] at he; norm_cast at he ⊢}; · {
 have hlo:1<((t:ℝ)+4)*alpha:=(by
 {have h:=(div_lt_iff₀ (by {positivity}:(0:ℝ)<(t:ℝ)+4)).mp hlow; nlinarith only [h]}); have
 hhi:((t:ℝ)+3)*alpha<1:=(by
 {have h:=(lt_div_iff₀ (by {positivity}:(0:ℝ)<(t:ℝ)+3)).mp hhigh; nlinarith only [h]}); have
 floors:(∀ k:ℕ, t+3≤ k→k≤2*t+2→⌊alpha+(k:ℝ)*alpha⌋=(1:ℤ)):=(by {
 intro k hklo hkhi; rw [Int.floor_eq_iff]; norm_num only [Int.cast_one]; have hloR:((t:ℝ)+3≤ k):=(by
 {exact_mod_cast hklo}); have hhiR:((k:ℝ)≤2*(t:ℝ)+2):=(by {exact_mod_cast hkhi}); constructor<;>
 nlinarith only [hlo, hhi, h0, hloR, hhiR]}); have zero:(⌊alpha⌋=(0:ℤ)):=(Int.floor_eq_zero_iff.mpr
 ⟨h0.le,h1⟩); have hu0:(u 0 ≠ true):=(by {
 intro hu; have h:=((lowerMechanicalWord_eq_true_iff alpha alpha 0).mp hu);
 dsimp only [lowerMechanicalLetter] at h; simp only
 [Nat.zero_add,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero] at h;
 rw [zero, Int.floor_eq_zero_iff.mpr ⟨by {positivity}, by {linarith only [h13]}⟩] at h;
 norm_num at h}); have huC:(u (2*t+1) ≠ true):=(by {
 intro hu; have h:=((lowerMechanicalWord_eq_true_iff alpha alpha (2*t+1)).mp hu);
 dsimp only [lowerMechanicalLetter] at h; rw [floors (2*t+1+1) (by {omega}) (by {omega}), floors
 (2*t+1) (by {omega}) (by {omega})] at h; norm_num at h}); have hcC:(c (2*t+1)=1):=(by {
 have h:=(lowerMechanicalWindowTrueCount_eq_floor (rho:=alpha) h0.le h1 0 (2*t+1));
 simp only [Nat.zero_add, Nat.cast_zero, zero_mul, add_zero] at h; rw [zero, floors (2*t+1) (by
 {omega}) (by {omega})] at h; change (c (2*t+1):ℤ)=_ at h; norm_num at h; exact_mod_cast h}); have
 hstart:((x 0).val=2):=(by {rw [label, if_neg hu0]; simp [paint,b]}); have hend:((x
 (2*t+1)).val=2):=(by {
 rw [label, if_neg huC]; have he:(b (2*t+1)=2*t):=(by {dsimp [b]; rw [hcC]; omega}); rw [he];
 simp [paint]}); have hperiod:(HasPeriod x (2*t+2) 0 (2*t+1)):=(by {
 intro k hk; have hk0:(k=0):=(by {omega}); subst k; simp only [Nat.zero_add]; exact (Fin.ext
 (hstart.trans hend.symm))}); simp only [show 2*t+3-1=2*t+2 by {omega},show 2*t+3-2=2*t+1 by
 {omega}]; unfold criticalExponent; exact (le_iSup_of_le (2*t+2) (le_iSup_of_le 0 (le_iSup_of_le
 (2*t+1) (le_iSup_of_le ⟨by {omega},by {omega},hperiod⟩ le_rfl))))}}}}
end D5.S1.Words.BalancedThreshold
