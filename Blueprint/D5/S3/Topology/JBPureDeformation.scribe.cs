using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class JBPureDeformationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized quadratic pullback preserves purity on the original complete real JB carrier. A pure state with zero first moment and positive second moment has nearby pure states with nonzero first moment, converging in the continuous dual norm.",
        H("Pure states under original quadratic deformation"),
        Blocks(
            Paragraph(Text("Let X be a complete real normed vector space, with specified bilinear product S, unit u, and the six laws Data(X,S,u): symmetry, unit multiplication, the Jordan identity, product norm domination, the square norm identity, and square norm monotonicity. No specialness, JC representation, finite dimension, separability, minimal projection or bidual is assumed. The zero algebra is included; it has no normalized state satisfying the hypotheses.")),
            Paragraph(Text("Let B be the continuous real functionals beta with beta(u)=1 and beta(S(x,x))>=0 for every x in the same X. Pure means membership in the real extreme points of B. Put L(h)z=S(h,z), U(a)z=2S(a,S(a,z))-S(S(a,a),z), Q(t)=I+2t L(h)+t^2 U(h)=U(u+th), and beta(t)=beta(Q(t)(u))^(-1) beta composed with Q(t). The scalar denominator is the actual transformed unit mass, not a fixed external normalization.")),
            Paragraph(Text("An algebraic positive normalized functional has abs(beta(x))<=norm(x): evaluate it on the original squares norm(x)u+x and norm(x)u-x. It therefore bundles as a continuous functional with precisely the same values and norm at most one. If it is extreme among the algebraic positive normalized functionals, every continuous convex decomposition is also such an algebraic decomposition, so the bundled functional belongs to the extreme points of B. No continuity premise is added to the original algebraic state by this representation.")),
            Describe.Lean(DescribeId.Create("original-pure-quadratic-deformation"),
                DeclarationHandle.Create("D5/S3/Topology/JBPureDeformation.pure_deformation"),
                H("Pure deformation with positive mass and norm convergence"),
                StatementSource.FromAuthor(F.Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume beta is pure, beta(h)=0, and q=beta(S(h,h))>0. For every sufficiently small nonzero real t, u+th is an actual square in X, U(u+th) is bijective on X, its transformed mass is positive, and beta(t) is pure. Writing r=beta(S(h,S(h,h))), its value on h is (2tq+t^2r)/(1+t^2q), which is nonzero for such t. The function beta(t) converges to beta in the norm of the continuous dual, hence also on each fixed target of X.")),
                    Paragraph(Text("The nonlinear normalization is handled by reweighting convex decompositions. For a cone C with strictly positive linear mass m on its nonzero elements, let T be a linear cone automorphism and x an extreme point of the mass-one base. If T(x)/m(T(x))=a y+b z, pull back y,z and normalize each separately. The new coefficients are m(T(x)) a m(T^(-1)y) and m(T(x)) b m(T^(-1)z). They are positive and sum to one by the original mass identity. Extremality forces both normalized pullbacks to equal x, and applying T and the mass identity forces y=z=T(x)/m(T(x)). This uses no affine transport claim for the normalized map.")),
                    Paragraph(Text("For the original JB square cone, positive functionals have positive unit mass unless they vanish: apply them to the actual squares norm(x)u+x and norm(x)u-x. Every U(a) preserves squares. If U(a) is bijective, choose b with U(a)b=u. The fundamental identity gives U(a) U(b) U(a)=I, so its inverse is U(b) U(a), which also preserves squares. Pullback on the continuous dual is therefore an actual linear cone automorphism, and the reweighting argument applies.")),
                    Paragraph(Text("The polynomial Q(t) is continuous in operator norm and equals I at zero. Openness of the units gives its local bijectivity. The original square-root criterion supplies u+th as a square near zero. The mass equals 1+t^2q. The numerator on h factors as t(2q+tr), with the second factor positive near zero. Continuous composition and inverse scalar mass give convergence in dual norm.")))),
            Paragraph(Text("In the original dense-domain response setting, take h to be the embedded original output D(mu u,b), and test the fixed target b Jordan h. This result changes only the mathematical state used to read that fixed target; it changes neither the original preparation family nor the total response or its domain. To infer a zero target reading one must separately prove the nonzero-first-moment contact approximation for every deformed pure state. Minimal pure-state support in the JB bidual, bounded original signed-square approximation, pure-state separation, the full unit row and its continuation remain separate obligations. The argument is a classical cone-base transport construction applied to the original JB quadratic map and makes no literature novelty claim.")))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) => new Formula.Apply(V(s), [.. a]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula P(Formula a, Formula b) => Call("S", a, b);
    private static Formula Beta(Formula a) => Call("beta", a);
    private static Formula Delta => Call("deformation", V("A"), V("beta"), V("h"), V("t"));
    private static Formula Q => Beta(P(V("h"), V("h")));
    private static Formula R => Beta(P(V("h"), P(V("h"), V("h"))));
    private static Formula At => Call("add", V("u"), Call("smul", V("t"), V("h")));
    private static Formula Value => Call("divide",
        Call("add", Call("multiply", F.D(2), V("t"), Q), Call("multiply", Call("square", V("t")), R)),
        Call("add", F.D(1), Call("multiply", Call("square", V("t")), Q)));
    private static Formula Local => Ex("epsilon", V("Real"), And(Lt(F.D(0), V("epsilon")),
        All("t", V("Real"), Imp(And(Lt(Call("abs", V("t")), V("epsilon")), Ne(V("t"), F.D(0))),
            And(Ex("a", V("X"), Eq(P(V("a"), V("a")), At)),
                And(Call("Bijective", Call("U", V("S"), At)),
                    And(Lt(F.D(0), Beta(Call("U", V("S"), At, V("u")))),
                        And(Call("mem", Delta, Call("extremePoints", V("Real"), Call("states", V("S"), V("u")))),
                            And(Eq(Call("apply", Delta, V("h")), Value), Ne(Call("apply", Delta, V("h")), F.D(0)))))))))));
    private static Formula Statement() => All("X", V("CompleteRealNormedSpaces"),
        All("S", Call("RealBilinearMaps", V("X")), All("u", V("X"), All("A", Call("Data", V("X"), V("S"), V("u")),
            All("beta", Call("ContinuousRealDual", V("X")),
                Imp(Call("mem", V("beta"), Call("extremePoints", V("Real"), Call("states", V("S"), V("u")))),
                    All("h", V("X"), Imp(Eq(Beta(V("h")), F.D(0)), Imp(Lt(F.D(0), Q),
                        And(Local, Call("TendstoInDualNormAtZero", Call("deformation", V("A"), V("beta"), V("h")), V("beta"))))))))))));
}
