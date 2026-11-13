using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ContinuousFrameSumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/ContinuousFrameSum.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Space => V("V");
    private static Formula Cone => V("C");
    private static Formula Unit => V("u");
    private static Formula P => C("pure", Cone, Unit);
    private static Formula K => C("base", Cone, Unit);
    private static Formula B => C("exclusionBalls", Cone, Unit);
    private static Formula W => C("weakPair", Cone, Unit);
    private static Formula G => C("commonCenter", V("hB"));
    private static Formula S(Formula p) => C("sumVector", V("hB"), p);
    private static Formula Orth(Formula p, Formula q) => C("excludes", Cone, Unit, p, q);
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", Space), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, Space), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, Space), CloseBracket, Sp,
        OpenBracket, C("Nontrivial", Space), CloseBracket, Sp,
        All("C", C("PointedCone", R, Space),
        All("u", C("LinearMap", R, Space, R),
        Imp(C("IsClosed", Cone), Imp(All("x",Space,Imp(In(V("x"),Cone),
        Imp(new Formula.Relation(V("x"),FormulaRelationOperator.NotEqual,D(0)),
        new Formula.Relation(D(0),FormulaRelationOperator.LessThan,C("apply",Unit,V("x")))))),
        Imp(Eq(C("span", R, Cone), C("top")), All("hB", B, body))))))));

    public DocumentDefinition Create()
    {
        Formula p = V("p"), q = V("q"), cap = V("U");
        Formula value = All("p", P, Eq(S(p),cap));
        Formula constant = Ex("U", Space, value);
        Formula ri = In(C("smul", C("div", D(1), D(3)), cap), C("intrinsicInterior", R, K));
        Formula interior = In(cap,C("interior",Cone));
        Formula a = Context(Imp(G,And(W,Ex("U",Space,And(value,And(ri,interior))))));
        Formula edge = All("p",P,All("q",P,Imp(Orth(p,q),Eq(S(p),S(q)))));
        Formula orthogonalPairs = Seq(OpenBrace,V("s"),Colon,P,Times,P,Mid,
            Orth(C("fst",V("s")),C("snd",V("s"))),CloseBrace);
        Formula closed = C("IsClosed",orthogonalPairs);
        Formula weakConsequences = And(closed,
            And(C("Continuous",C("sumVector",V("hB"))),And(edge,Iff(G,constant))));
        Formula b = Context(And(Imp(W,weakConsequences),Imp(C("pairProper",Cone,Unit),G)));
        Formula compact = Context(Imp(W,C("IsCompact",P)));
        Formula definitions = And(
            Eq(K,C("normalizedConeBase",Cone,Unit)),
            And(Eq(P,C("extremePoints",R,K)),And(
                Eq(C("center",V("hB"),p),C("apply",C("chosenExclusionChart",V("hB"),p),D(0))),
                Eq(S(p),C("add",p,C("smul",D(2),C("center",V("hB"),p)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Original EB and common centers force weakPair and interior; original W supplies compact pure points and continuous frame sums.",
            H("Original common centers and continuous frame sums"),Blocks(
                Describe.Lean(DescribeId.Create("effects-compact"), DeclarationHandle.Create(Owner + "effects_compact"), H("Compactness of the full original effect interval"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every finite dimensional real normed V, original pointed cone C and linear unit u, strict positivity of u on nonzero cone vectors and span(C)=top imply compactness of the entire original interval effects(C,u)={f : V toL R : proper(C,u,f)}. The original proof and telescope are unchanged. ExclusionIncidence.exclusion_upper_limit directly consumes this fact to obtain a subsequential limit of actual full-interval confirming effects. Neither Pair nor closedness of the pure carrier is needed."))), DescribeRole.Theorem),
                Paragraph(Text("The original carrier is any nonzero finite-dimensional real V, with closed generating cone C and the same strictly positive unit u. K is the whole normalized base, P is ALL its extreme points and [0,u] is the entire original proper-effect interval. No finite carrier, selected menu, assumed compact P, closed orthogonality, common intersection or positive-extension premise is used.")),
                Describe.Lean(DescribeId.Create("original-centers"),DeclarationHandle.Create(Owner+"sumVector"),H("Original centers and frame carrier"),StatementSource.FromAuthor(Disp(Context(All("p",P,definitions)))),
                    AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("exclusionBalls supplies, at every original pure p, an injective affine parametrization of ALL D_p by a finite Euclidean closed unit ball of positive dimension. center is the image of zero in a chosen such chart. sumVector(p)=p+2 center(p) is the original U(p). commonCenter quantifies equality of these vectors over ALL original pure p,q. The frame-sum argument identifies this chart center with the midpoint of every original orthogonal diameter; no frame-fiber sum is assumed.")),
                        Paragraph(Text("effects uses continuous linear maps to represent the original full proper interval. Every real linear map on finite-dimensional V has its native continuous-linear representation, so this does not restrict the original effects. frames initially permits three arbitrary original states with three full proper effects, delta readings, and their linear-map sum exactly u. Purity of the three states is derived where needed; it is not built into that raw compact frame carrier."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("pure-compact"),DeclarationHandle.Create(Owner+"original_pure_compact"),
                    H("Original W forces compactness of all pure points"),StatementSource.FromAuthor(Disp(compact)),
                    AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("The hypotheses are original closedness, strict positivity, generation, EB_ge1 and weakPair. Pure-point compactness is a conclusion. A generating cone has nonempty interior by the existing affine-span criterion. Choose an interior point v and a ball radius, and evaluate any proper effect at v plus and minus a small unit vector. Nonnegativity at both points bounds its operator norm uniformly by u(v) divided by that small radius. The original proper-effect interval is closed, hence compact by the existing finite-dimensional closed-bounded criterion.")),
                        Paragraph(Text("The full raw-frame constraints are closed in the compact product of three original bases and three entire effect intervals. Joint completion is supplied by OrthogonalJointCompletion.whole_joint_completion on the original all-P domain. It also gives injectivity of p to D_p: after completing p to p,r,s, equal exclusions put both owners into the singleton intersection D_r intersect D_s.")),
                        Paragraph(Text("For a raw frame, consider the exposed one-value face of its first effect. Its other two states are different because another effect distinguishes them. For any two pure points in that one-value face, both other states lie in both exclusions. chart_face_eq makes those exclusions equal, and injectivity makes the two pure points equal. The existing compact-face Krein-Milman result then makes the entire one-value face a singleton, proving the first raw vertex pure. Conversely every original pure point is the first vertex of a raw frame by the original joint theorem. Thus P is precisely a continuous projection of the compact raw-frame set. The conclusion uses the derived purity of raw-frame vertices; compact projection and Krein-Milman are existing library results."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("continuous-frame-sum"),DeclarationHandle.Create(Owner+"original_continuous_frame_sum"),
                    H("Continuity, all original orthogonal edges, and full Pair"),StatementSource.FromAuthor(Disp(b)),
                    AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("On the original P squared the existential proper-effect witness relation is closed. This follows by projecting the closed one-zero evaluation constraints through the compact ENTIRE effect interval, using the existing closed-projection theorem. For two original orthogonal pure points q,r in an entire D_p, native sphere coordinates and the public affine_zero_antipode theorem force their coordinates to be antipodal. Affine midpoint preservation then gives q+r=2 center(p). Applied to an original joint triple, this proves p+q+r=U(p)=U(q), hence constancy on EVERY original orthogonal edge.")),
                        Paragraph(Text("Restrict raw frames to those whose three vertices are original pure points. The derived compactness of P makes this restriction compact. Its first-vertex projection is continuous and surjective onto ALL P. Joint completion and its singleton intersection identify any frame's third point with the original joint third point, so U composed with this projection is exactly the continuous sum of the three vertices. Continuity descends through the existing compact closed-map quotient criterion and quotient continuity theorem. No generic continuity lemma is re-proved or counted as new mathematics, and neither carrier compactness nor fiber sums are additional hypotheses.")),
                        Paragraph(Text("commonCenter is equivalent to a single vector value on ALL P; nonemptiness follows from pure_span and nontriviality. Full Pair gives weakPair because an original orthogonal pair is distinct. Under full Pair, the existing complete proper-face classifier gives H(p,q)=D_s for every distinct original pair. Original zero symmetry places s in both original exclusions, yielding two original orthogonal edges through s. Their equalities give U(p)=U(q). Thus the full-Pair implication uses an actually derived common pure point, rather than assuming a common intersection or a covering law."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("common-center-interior"),DeclarationHandle.Create(Owner+"common_center_interior"),
                    H("EB plus G suffices on the original domain"),StatementSource.FromAuthor(Disp(a)),
                    AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("This theorem assumes only the original cone data, EB_ge1 and commonCenter. weakPair is a CONCLUSION. Every U(p) equals one U, and w=U/3 is an original state because w=(p+2 center(p))/3. If w were outside the cone interior, the existing Hahn-Banach support theorem would supply a nonzero linear functional maximizing there. Cone scaling forces its maximum to be zero. Every original p and center(p) then has nonpositive value; the common-center equation forces the value of every p to be zero. Since ALL original pure points span V, the functional is zero, a contradiction. Hence w is in the cone interior; positive scaling gives U in the cone interior. Restricting an open cone neighborhood to the affine span of the normalized base gives w in its intrinsic, or relative, interior.")),
                        Paragraph(Text("For an original p orthogonal to q, take q's antipode r in ALL D_p. Its purity follows from the original exclusion faciality and the sphere extreme-point image theorem. Choose an original common zero confirmer a_q from the EB face theorem. G gives a_q(U)=1, original zero symmetry gives a_q(p)=0, and the antipodal affine identity U=p+q+r gives a_q(r)=0. Thus r belongs to BOTH D_p and D_q. Zero symmetry puts p,q in D_r. The native cone-face lift of D_r now contains their whole original minimal face, which is therefore proper. This proves weakPair directly, without first invoking W.")),
                        Paragraph(Text("Together these declarations cover the full original VII105.9 statement and its explicit U-interior conclusion. They do not assume pure compactness, original orthogonality closedness, frame completion, global common intersections or the separate positive-extension theorem VII105.4. No assertion of physical realization or reconstruction is made."))),DescribeRole.Theorem))));
    }
}
