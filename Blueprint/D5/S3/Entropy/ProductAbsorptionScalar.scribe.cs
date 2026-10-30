using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class ProductAbsorptionScalarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/ProductAbsorptionScalar.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/local2026productabsorption");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete closed-domain product absorption scalar inequality uses actual natural-log binary entropy.",
        H("Binary-Entropy Product Absorption"), Blocks(
            Node("phaseNoiseEntropy", "Binary phase-noise entropy", DescribeRole.Definition,
                All("b", All("t", Equal(E(N("t")), Call("binEntropy", Frac(Add(D(1), Call("sqrt",
                    Add(Pow(N("b")), Multiply(Subtract(D(1), Pow(N("b"))), Pow(N("t")))))), D(2)))))),
                "For real b,t, phaseNoiseEntropy(b,t)=binEntropy((1+sqrt(b^2+(1-b^2)t^2))/2). "
                + "Its intended entropy scope is 0<=b<=1 and -1<=t<=1. The definition is total on real inputs."),
            Node("product_binary_entropy_absorption", "The complete scalar inequality", DescribeRole.Theorem,
                Statement(), "For all z,w in [-1,1] and b in [0,1], put l=zw and "
                + "T=sqrt((1-z^2)(1-w^2)). Then F_b(z)+F_b(w)-2F_b(l)+(F_b(l+T)+F_b(l-T))/2>=0, "
                + "where F_b(t)=phaseNoiseEntropy(b,t) is the actual binary entropy from the definition. "
                + "Every sign and every endpoint b=0,1 and z,w=0,+1,-1 is included, as are zero and coincident roots."),
            Paragraph(Text("Set u=1-z^2, v=1-w^2 and c=1-b^2. Write A=u+v, B=uv, L=A-B, "
                + "q=sqrt(B(1-A+B)), Mplus=A-2B+2q and Mminus=A-2B-2q. These parameters lie in [0,1]. "
                + "For F(x)=binEntropy((1+sqrt(1-x))/2), the exact scalar expression becomes "
                + "F(cu)+F(cv)-2F(cL)+(F(cMplus)+F(cMminus))/2.")),
            Paragraph(Text("For c>0, the exact logarithmic entropy integral and substitution s=ct give "
                + "c/4 times the integral of K(u,v,t)/sqrt(1+ct) on t>0. All five scaled entropy "
                + "integrands are absolutely integrable. The unweighted kernel K is absolutely integrable "
                + "and has nonnegative integral by the preceding moment theorem. It is either nonnegative "
                + "or changes sign once from positive to negative at r>0. The weight w_c(t)=1/sqrt(1+ct) "
                + "is positive, bounded by one and decreasing. Thus K(t)w_c(t)>=K(t)w_c(r) pointwise, "
                + "and the weighted integral is at least w_c(r) times the nonnegative unweighted integral. "
                + "At c=0 the entropy expression is zero.")),
            Paragraph(Text("For the exact coordinate return, L=1-l^2, T^2=B and q=abs(l)*T. "
                + "Hence the unordered pair {Mplus,Mminus} is {1-(l+T)^2,1-(l-T)^2}; the sign of l "
                + "only changes their order. The identity F((1-b^2)(1-t^2))=F_b(t) then gives the displayed "
                + "closed-domain inequality directly. No numerical quadrature, generic concavity surrogate, "
                + "or extra entropy hypothesis supplies its sign.")),
            Paragraph(Text("This substantive scalar theorem is a product component of the larger quantum question. "
                + "A conclusion about arbitrary normalized complex product density seeds still needs the exact "
                + "Gram-isospectral entropy bridge, the explicit local noise-record CPTP map, mutual-information "
                + "data processing, the sharp attained D* formula and actual partial-trace entropy identities. "
                + "It does not settle entangled seeds, mixed seeds or the original full quantum Zhang--Yeung question. "
                + "The source is the task-supplied local unpublished scalar proof.")))));

    private static DocumentBlock Node(string n, string title, DescribeRole role, Formula f, string prose) =>
        Describe.Lean(DescribeId.Create("product-scalar-" + n.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + n), H(title), StatementSource.FromAuthor(Disp(f)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static Formula N(string n) => F.Id(n);
    private static Formula R() => Seq(Mathbb, Grp(N("R")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x) => Seq(Par(x), Caret, Grp(D(2)));
    private static Formula All(string n, Formula x) => Seq(Forall, Sp, Par(Seq(N(n), Colon, Sp, R())), Comma, Sp, x);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, y);
    private static Formula Inside(Formula x, Formula a) => And(Le(a, x), Le(x, D(1)));
    private static Formula E(Formula x) => Call("phaseNoiseEntropy", N("b"), x);
    private static Formula L() => Multiply(N("z"), N("w"));
    private static Formula T() => Call("sqrt", Multiply(Subtract(D(1), Pow(N("z"))), Subtract(D(1), Pow(N("w")))));
    private static Formula HValue() => Add(Subtract(Add(E(N("z")), E(N("w"))), Multiply(D(2), E(L()))),
        Frac(Add(E(Add(L(), T())), E(Subtract(L(), T()))), D(2)));
    private static Formula Statement() => All("z", All("w", All("b", Imp(Inside(N("z"), Seq(Minus, D(1))),
        Imp(Inside(N("w"), Seq(Minus, D(1))), Imp(Inside(N("b"), D(0)), Le(D(0), HValue())))))));
}
