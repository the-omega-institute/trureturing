using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class JBAmbientSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ambient order domination by an idempotent forces support in its Peirce two-space on the original complete real six-law JB carrier.",
        H("Ambient idempotent support"),
        Blocks(
            Paragraph(Text("Let X be any complete real normed vector space, S its specified real bilinear product, and u its specified unit. Data(X,S,u) consists of symmetry, the unit law, the Jordan identity, product norm domination, the square norm identity and square monotonicity. Write K(y) for the existence of z in this same X with S(z,z)=y, and write U(r,y)=2 S(r,S(r,y))-S(S(r,r),y). The zero space and zero idempotent are included.")),
            Describe.Lean(DescribeId.Create("ambient-idempotent-support"),
                DeclarationHandle.Create("D5/S3/Topology/JBAmbientSupport.support_of_squares"),
                H("Domination forces support"), StatementSource.FromAuthor(F.Disp(Scope(
                    All("p", V("X"), All("x", V("X"), All("c", V("Reals"),
                    Imp(And(Idempotent, And(K(Add(CP, V("x"))), K(Sub(CP, V("x"))))),
                    Eq(P(V("p"), V("x")), V("x"))))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Set q=u-p and g(t)=U(u+tq,cp+x), h(t)=U(u+tq,cp-x). The original quadratic positivity theorem makes g(t) and h(t) actual squares for every real t. Bilinear expansion gives g(t)+h(t)=2cp and g(t)-g(-t)=4t S(q,x). Square monotonicity gives norm(g(t))<=2 norm(cp), hence abs(t) norm(S(q,x))<=norm(cp) uniformly in t. If S(q,x) is nonzero, t=(norm(cp)+1)/norm(S(q,x)) contradicts this bound. Therefore S(q,x)=0 and S(p,x)=x. No sign restriction on c is needed for this implication.")))),
            Describe.Lean(DescribeId.Create("supported-ambient-bounds"),
                DeclarationHandle.Create("D5/S3/Topology/JBAmbientSupport.squares_of_supported"),
                H("The original norm bounds supported vectors"), StatementSource.FromAuthor(F.Disp(Scope(
                    All("p", V("X"), All("x", V("X"),
                    Imp(And(Idempotent, Eq(P(V("p"), V("x")), V("x"))),
                    And(K(Add(Scale(N(V("x")), V("p")), V("x"))),
                        K(Sub(Scale(N(V("x")), V("p")), V("x")))))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The original ambient center theorem makes norm(x)u+x and norm(x)u-x squares. Apply the original positive quadratic map U(p), which sends u to p and fixes x. Thus both norm(x)p+x and norm(x)p-x are actual ambient squares. Together with domination forcing support, this identifies the Peirce two-space with the vectors bounded above and below by a nonnegative scalar multiple of p. It does not assert equality with the corner's internal square cone.")))),
            Describe.Lean(DescribeId.Create("corner-square-bound"),
                DeclarationHandle.Create("D5/S3/Topology/JBAmbientSupport.corner_square_bound"),
                H("The square bound in the same ambient cone"), StatementSource.FromAuthor(F.Disp(Scope(
                    All("p", V("X"), All("a", V("X"),
                    Imp(And(Idempotent, Eq(P(V("p"), V("a")), V("a"))),
                    K(Sub(Scale(Call("square", N(V("a"))), V("p")), P(V("a"), V("a")))))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Specializing the existing polarized Jordan identity to p,p,a,a gives S(p,S(a,a))=S(a,a). The preceding supported-vector bound applied to S(a,a), and the original square norm identity, give norm(a)^2 p-S(a,a) as an actual square. Its root is required only in X. These consequences use the original product and norm and impose no square-root closure on a dense original subalgebra.")))))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(V(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula P(Formula x, Formula y) => Call("S", x, y);
    private static Formula K(Formula x) => Call("K", x);
    private static Formula N(Formula x) => Call("norm", x);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Scale(Formula x, Formula y) => Call("scale", x, y);
    private static Formula CP => Scale(V("c"), V("p"));
    private static Formula Idempotent => Eq(P(V("p"), V("p")), V("p"));
    private static Formula Scope(Formula body) => All("X", V("CompleteRealNormedSpaces"),
        All("S", Call("RealBilinearMaps", V("X")), All("u", V("X"),
        Imp(Call("Data", V("X"), V("S"), V("u")), body))));
}
