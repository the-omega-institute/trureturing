using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinFactor;

internal sealed class OriginalResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The residual on all original spin inputs",
        H("Two exact circles and saturated evaluation faces"),
        Blocks(
            Paragraph(Text("E, its Jordan product, cone, original norm, positive evaluations, P2 and PB are exactly those of OriginalDContract. D is the same arbitrary total function in every inner and outer occurrence. A positive evaluation has arbitrary mass m and vector v with vnorm(v) at most m; P2 retains both directed entries of its complex two-label table. The residual argument selects unit-mass boundary evaluations from this original family. It adds no additivity, homogeneity, continuity, unit-row, translation, three-label positivity or realization premise.")),
            Paragraph(Text("The additional conditional input is precisely one global pure orientation: there exists a real e, equal to 1 or -1, such that D((0,x),(0,y))=(0,e times cross(x,y)) for every original x,y. The result extends that very same e to every scalar/vector input. It does not derive the pure input from P2 and PB, and hence does not by itself establish the P2/PB-only classification or its converse.")),
            Paragraph(Text("For fixed e, F(s,t,x,y)=D((s,x),(t,y))-(0,e times cross(x,y)). The known Cayley preimage B of x at q is (x-e times cross(q,x)+dot(q,x) times q)/(1+dot(q,q)). It satisfies B+e cross(q,B)=x and dot(q,B)=dot(q,x). The Cayley image is B-e cross(q,B). All denominators are positive. These are formulas for known vector operations, not an inverse or extension of D.")),
            Paragraph(Text("Take PB on the three pure inputs q,B,C. The two original outer pairs are (-dot(q,C), B+e cross(q,B)), (dot(q,B), C+e cross(q,C)) and their opposite-sign versions. The Jordan correction in the finite difference equals the difference of their fixed cross outputs. Their residuals therefore agree. Applying the existing exact label half-turn restores the original two scalars and negates the opposite Cayley vector images. Every finite q satisfying dot(q,x)=t and dot(q,y)=-s gives a fixed-output residual identity.")),
            Paragraph(Text("An arbitrary determinant-one isometry R fixing k=s x+t y+e cross(x,y) admits the required finite substitution without a continuity argument. If R x=x, the axis equation and preservation of dot(x,y) force R y=y. Otherwise put B=(x-R x)/2, U=(x+R x)/2, C=(y-R y)/2 and V=(y+R y)/2. The equal first norm gives dot(B,U)=0, and the equal mixed Gram entry gives dot(B,V)+dot(U,C)=0. With A=dot(B,B)>0, choose q=(t/A)B+(e/A)cross(B,U). Then dot(q,B)=t and cross(q,B)=e U. The fixed-axis equation gives dot(q,C)=-s and cross(q,C)=e V. Thus the two opposite Cayley images are exactly -R x and -R y. This proves the complete circle law, including identity and half-turn rotations.")),
            Paragraph(Text("Swapping the two original inputs preserves s x+t y and reverses cross(x,y). Skew symmetry of the original D therefore supplies the second complete circle, about s x+t y-e cross(x,y). If cross(x,y) is nonzero and s,t are not both zero, the vector s x+t y is nonzero and perpendicular to cross(x,y). The Gram determinant of these two axes is strictly positive. The supplied TwoAxisFiniteRotation.moving_axis_invariance applies at every actual rotated pair: its two current axes are the images of the original axes. Its exact finite words give fixed-output invariance under every determinant-one isometry. No action is applied to the residual output, and no unknown function is assumed equivariant or continuous.")),
            Paragraph(Text("Write the fixed residual as (delta,z), w=cross(x,y) and p=s y-t x. At a unit n, the original determinant inequality is the squared bound by dot(w+cross(n,p),w+cross(n,p)). Rotating the original inputs and evaluating along the same rotated n leaves the known right side and e dot(n,w) unchanged, while the extra readout becomes dot(R n,z). Twelve explicit determinant-one signed coordinate permutations suffice to compare this extra readout. Four sign choices isolate a single coordinate product, and the three cyclic permutations move every coordinate of n to every coordinate of z. Since some coordinate of a unit three-vector has absolute value at least 1/2, for each coordinate i the resulting bound is abs(delta+e dot(n,w))+(1/2)abs(z_i) at most vnorm(w+cross(n,p)), for every unit n. This finite family is used inside the all-input argument; the input domain and the evaluation family remain unrestricted.")),
            Paragraph(Text("The support calculation takes arbitrary perpendicular w,p with w nonzero. Put a=dot(w,w)>0, b=dot(p,p), c=cross(w,p). When a is at most b, choose n=(c+sqrt(b-a)p)/b. It has squared norm one, dot(n,w)=0 and cross(n,p)=-w, so the support bound reads abs(delta)+Z at most zero. This includes a=b. When b<a, set J=sqrt(a-b) and n_plus=(c+J w)/a, n_minus=(c-J w)/a. Both are unit, dot(n_plus,w)=J, dot(n_minus,w)=-J, and both right-side norms equal J. The two bounds force delta=0 and Z=0 for either e. Taking Z=(1/2)abs(z_i) for each coordinate gives z=0. The case p=0 is included in the second branch.")),
            Paragraph(Text("Collinear vector parts, including either zero vector, use the existing original collinear-zero theorem for every scalar pair. If both scalars vanish, the explicit pure conclusion applies directly. The remaining branch uses the two circles and saturated support. Thus arbitrary signs, unequal lengths, unit vectors, zero and proportional inputs all retain their original values and the one fixed orientation. Matrix consumers, the reverse implication, neutrality, bilinearity, continuity, all finite complex Gram tables and original R require their separate same-D integration.")),
            Describe.Lean(
                DescribeId.Create("original-residual-value"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalResidual.residual"),
                H("Residual in the original output space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every total D, real e,s,t and original vectors x,y, residual(D,e,s,t,x,y) is D((s,x),(t,y)) minus (0,e times cross(x,y))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-residual-rotation"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalResidual.rotate"),
                H("Original coordinates of a known Euclidean rotation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Euclidean linear isometric equivalence R and original vector x, rotate(R,x) applies R to the same three real coordinates through the standard Euclidean type wrapper and returns the original vector carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-residual-cayley-preimage"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalResidual.cayleyPreimage"),
                H("Known finite Cayley inverse formula"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real e and vectors q,x, the value is (x-e cross(q,x)+dot(q,x)q)/(1+dot(q,q)). When e equals 1 or -1, it is the inverse image of x under v mapping to v+e cross(q,v)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-residual-cayley-image"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalResidual.cayleyImage"),
                H("Opposite Cayley image"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real e and vectors q,x, put B=cayleyPreimage(e,q,x). The image is B-e cross(q,B)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-residual-finite-cayley-law"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalResidual.cayley_residual"),
                H("Pure PB triples fix the Cayley residual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every total D satisfying original P2 and PB, real e equal to 1 or -1, and the same-D pure formula for every x,y, the following holds for every real s,t and all x,y,q satisfying dot(q,x)=t and dot(q,y)=-s: F(s,t,x,y)=F(s,t,-cayleyImage(e,q,x),-cayleyImage(e,q,y)). No nonzero, independence or scalar restriction is imposed on this finite-parameter law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-residual-full-circle"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalResidual.local_full_circle"),
                H("Every rotation about the first residual axis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D satisfying original P2 and PB, real e equal to 1 or -1 and its same-D all-pure formula, every real s,t, every x,y with cross(x,y) nonzero, and every determinant-one Euclidean isometry R fixing s x+t y+e cross(x,y), one has F(s,t,rotate(R,x),rotate(R,y))=F(s,t,x,y). The identity rotation is included and s,t may both be zero. The second axis follows by swapping the two original inputs and using skew symmetry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-residual-saturated-support"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalResidual.saturated_support_zero"),
                H("Saturated faces eliminate a fixed additive residual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real e,delta,Z with e equal to 1 or -1 and Z nonnegative, and every nonzero original vector w and perpendicular vector p, suppose for every unit vector n that abs(delta+e dot(n,w))+Z is at most vnorm(w+cross(n,p)). Then delta=0 and Z=0. The vector p may vanish, and all comparisons of the two vector lengths, including equality, are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-residual-all-inputs"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalResidual.all_inputs_of_pure"),
                H("One pure sign extends to all original scalar/vector inputs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every arbitrary total D on the original E, assume the original all-evaluation directed complex P2, the literal same-D PB, and the explicit conclusion that there exists a real e equal to 1 or -1 with D((0,x),(0,y))=(0,e cross(x,y)) for every x,y. Then there exists such an e with D((s,x),(t,y))=(0,e cross(x,y)) for all real s,t and all original x,y. The proof retains the sign selected by the pure premise and handles every degenerate input. There is no additional geometric, regularity or physical premise. The derivation of the pure premise, the original-P2/PB-only iff and its same-D consequences remain separate assertions."))),
                DescribeRole.Theorem))));
}
