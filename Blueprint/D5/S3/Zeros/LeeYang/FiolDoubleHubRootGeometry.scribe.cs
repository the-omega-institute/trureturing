using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class FiolDoubleHubRootGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical double-hub family: rootgeometry.",
        H("Double-hub rootgeometry"), Blocks(
            Paragraph(Text("The intermediate value theorem produces one phase zero in each interval with opposite endpoint signs. Exponentiation is injective on the open upper semicircle. Real coefficients supply conjugate lower roots; the two families are disjoint. A degree bound of 2N then exhausts the polynomial and proves simplicity.")),
            Paragraph(Text("The exact b-grid values at d=2 are -21 and 216; at d=3 they are -82 and 234; at d=4 they are 42-69sqrt(5),42+69sqrt(5),2952. These boundary evaluations join the uniform d>=5 sign estimate.")),
            Paragraph(Text("For residue 3 modulo 4, an intermediate value solution of v+ell*u=0 lies in the central gap and has positive phase, because the resulting g_d(t)u^2 is strictly positive. For residue 2 the negative derivative at pi/2 gives a nearby positive point on the left and negative point on the right, including d=2.")),
            Paragraph(Text("These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.")),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-exp-upper-injective"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.exp_upper_injective"), H("exp upper injective"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem exp_upper_injective :     Set.InjOn (fun x : \u211d => Complex.exp ((x:\u2102)*Complex.I)) (Set.Icc 0 Real.pi)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-roots-from-alternating-samples"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.roots_from_alternating_samples"), H("roots from alternating samples"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs an ordered root in each disjoint interval from strict sign alternation. Exact source statement: theorem roots_from_alternating_samples (d n : \u2115) (hd : 2 \u2264 d)     (s : Fin (n+1) \u2192 \u211d) (hmono : StrictMono s)     (hbound : \u2200 j, 0 \u2264 s j \u2227 s j \u2264 Real.pi)     (hsign : \u2200 j : Fin n,       (phaseValue d (s j.castSucc)).re*(phaseValue d (s j.succ)).re < 0) :     \u2203 theta : Fin n \u2192 \u211d,       (\u2200 j, s j.castSucc < theta j \u2227 theta j < s j.succ) \u2227       StrictMono theta \u2227       (\u2200 j, 0 < theta j \u2227 theta j < Real.pi \u2227         ((Q d).map Complex.ofRealHom).IsRoot (Complex.exp ((theta j:\u2102)*Complex.I)))."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-roots-exhausted-by-upper-family"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.roots_exhausted_by_upper_family"), H("roots exhausted by upper family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs disjoint upper/conjugate root multisets and exhausts the exact degree. Exact source statement: theorem roots_exhausted_by_upper_family (p : Polynomial \u211d) (n : \u2115)     (hp : p \u2260 0) (hdeg : p.natDegree \u2264 2*n) (r : Fin n \u2192 \u2102)     (hrinj : Function.Injective r) (hrupper : \u2200 j, 0 < (r j).im)     (hrroot : \u2200 j, (p.map Complex.ofRealHom).IsRoot (r j)) :     (p.map Complex.ofRealHom).roots =       Finset.univ.val.map r + Finset.univ.val.map (fun j => star (r j)) \u2227     (p.map Complex.ofRealHom).roots.Nodup."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-phasevalue-half-pi-negative"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.phaseValue_half_pi_negative"), H("phaseValue half pi negative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem phaseValue_half_pi_negative (d : \u2115) (hd : 2 \u2264 d) (hi : d%4 \u2260 2) :     (phaseValue d (Real.pi/2)).re < 0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-small-b-grid-values"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.small_b_grid_values"), H("small b grid values"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Discharges the exact d=2,3,4 numerical premises of the uniform sign proof. Exact source statement: theorem small_b_grid_values :     phaseValue 2 (Real.pi/3) = -21 \u2227 phaseValue 2 Real.pi = 216 \u2227     phaseValue 3 (Real.pi/2) = -82 \u2227 phaseValue 3 Real.pi = 234 \u2227     phaseValue 4 (Real.pi/5) = ((42-69*Real.sqrt 5:\u211d):\u2102) \u2227     phaseValue 4 (3*Real.pi/5) = ((42+69*Real.sqrt 5:\u211d):\u2102) \u2227     phaseValue 4 Real.pi = 2952."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-odd-b-sign-large"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.odd_b_sign_large"), H("odd b sign large"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem odd_b_sign_large (d j : \u2115) (hd : 5 \u2264 d) (ho : Odd d)     (hj : 1 \u2264 j) (hjd : 2*j \u2264 d+1) :     let b := 2*Real.pi*(j:\u211d)/((d:\u211d)+1)     if 4*j \u2264 d+1 then (phaseValue d b).re < 0 else 0 < (phaseValue d b).re."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-even-b-sign-large"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.even_b_sign_large"), H("even b sign large"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem even_b_sign_large (d j : \u2115) (hd : 5 \u2264 d) (ho : \u00ac Odd d)     (hj : 1 \u2264 j) (hjd : 2*j \u2264 d+2) :     let b := (2*(j:\u211d)-1)*Real.pi/((d:\u211d)+1)     if 2*(2*j-1) \u2264 d+1 then (phaseValue d b).re < 0 else 0 < (phaseValue d b).re."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-actual-central-derivative"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.actual_central_derivative"), H("actual central derivative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem actual_central_derivative (r : \u2115) :     HasDerivAt (fun theta : \u211d => (phaseValue (4*r+2) theta).re)       (-8*(4*(r:\u211d)+2)^4-16*(4*(r:\u211d)+2)^2*(2*(4*(r:\u211d)+2)-1)) (Real.pi/2)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-actual-central-two-sides"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.actual_central_two_sides"), H("actual central two sides"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Repairs the residue2 central grid with actual phase derivative evidence. Exact source statement: theorem actual_central_two_sides (r : \u2115) (a b : \u211d)     (ha : a < Real.pi/2) (hb : Real.pi/2 < b) :     \u2203 l q : \u211d, a < l \u2227 l < Real.pi/2 \u2227 Real.pi/2 < q \u2227 q < b \u2227       0 < (phaseValue (4*r+2) l).re \u2227 (phaseValue (4*r+2) q).re < 0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubrootgeometry-central-gap-residue-three"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.central_gap_residue_three"), H("central gap residue three"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uses IVT and simultaneous-nonzero/positivity facts to construct the missing central positive sample. Exact source statement: theorem central_gap_residue_three (r : \u2115) :     \u2203 c : \u211d, Real.pi/2 < c \u2227 c < 2*Real.pi*((r:\u211d)+1)/(4*(r:\u211d)+3) \u2227       0 < (phaseValue (4*r+3) c).re."))), DescribeRole.Theorem))));
}
