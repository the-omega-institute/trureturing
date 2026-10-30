using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class ProductAbsorptionLogIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/ProductAbsorptionLogIntegral.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/local2026productabsorption");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact logarithmic kernel is absolutely integrable and its integral is its five-term logarithmic moment.",
        H("The Product Absorption Logarithmic First Moment"),
        Blocks(
            Paragraph(Text("For real u and v put A=u+v, B=uv, L=A-B, q=sqrt(B(1-A+B)), "
                + "Mplus=A-2B+2q, and Mminus=A-2B-2q. Let K(u,v,s) be productLogKernel from "
                + "ProductAbsorptionLogKernel. When 0<=u,v<=1, L, Mplus and Mminus are nonnegative. "
                + "The real logarithm is natural and total; multiplication by zero gives 0log0=0.")),
            Node("productLogMoment", "The exact first moment", DescribeRole.Definition,
                AllReal("u", AllReal("v", Equal(Moment(), MomentBody()))),
                "This definition is a total real function. Its use as an integral moment concerns the closed unit square."),
            Node("product_log_kernel_integrable_integral", "Absolute integrability and exact integral", DescribeRole.Theorem,
                AllReal("u", AllReal("v", Imp(Inside(N("u")), Imp(Inside(N("v")), And(
                    Call("IntegrableOn", KernelFunction(), PositiveHalfLine()), Equal(Integral(), Moment())))))),
                "For every u and v in [0,1], K(u,v,.) is absolutely Lebesgue integrable on (0,infinity), "
                + "and its integral equals the displayed logarithmic moment. The measure is Lebesgue volume. "
                + "All parameter endpoints and the coincident-root case Mminus=0 are included."),
            Paragraph(Text("For x>=0 use the continuous primitive P(x,s)=(s+x)log(s+x)-slog(s). "
                + "For s>0 its derivative in s is log(1+x/s). The shifted primitive "
                + "P(x,s)-xlog(s)=(s+x)log(1+x/s) lies between x and x+x^2/s, "
                + "by 1-1/t<=log(t)<=t-1 for t>0. It therefore tends to x at infinity, including x=0.")),
            Paragraph(Text("Combine these primitives with coefficients 1,1,-2,1/2,1/2 at u,v,L,Mplus,Mminus. "
                + "The identity u+v-2L+(Mplus+Mminus)/2=0 cancels both the log(s) terms and their limiting constants. "
                + "Thus the combined primitive tends to zero. At s=0 it equals minus productLogMoment(u,v). "
                + "If the kernel is nonnegative, the nonnegative-derivative improper FTC supplies integrability. "
                + "Otherwise its unique crossing r splits the domain into a nonnegative-derivative interval (0,r] "
                + "and a nonpositive-derivative tail (r,infinity). The two FTC integrability results combine "
                + "to absolute integrability on the whole positive half-line. The improper FTC then gives the exact integral.")),
            Paragraph(Text("This theorem proves the integral identity and absolute integrability. It does not prove "
                + "that productLogMoment is nonnegative. The normalized concavity argument for that sign, "
                + "the binary-entropy integral representation, the decreasing-weight argument, the complete scalar H inequality, "
                + "and the spectral density/channel absorption endpoint remain separate obligations. "
                + "The primitive argument is a formal implementation of the local unpublished scalar input, "
                + "using the preceding kernel crossing theorem to establish absolute integrability.")))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("product-absorption-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static Formula N(string name) => F.Id(name);
    private static Formula R() => Seq(Mathbb, Grp(N("R")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula AllReal(string name, Formula body) => Seq(Forall, Sp,
        Par(Seq(N(name), Colon, Sp, R())), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Inside(Formula x) => And(Le(D(0), x), Le(x, D(1)));
    private static Formula A() => Add(N("u"), N("v"));
    private static Formula B() => Multiply(N("u"), N("v"));
    private static Formula L() => Subtract(A(), B());
    private static Formula Q() => Call("sqrt", Multiply(B(), Add(Subtract(D(1), A()), B())));
    private static Formula Root(bool plus) => plus
        ? Add(Subtract(A(), Multiply(D(2), B())), Multiply(D(2), Q()))
        : Subtract(Subtract(A(), Multiply(D(2), B())), Multiply(D(2), Q()));
    private static Formula MulLog(Formula x) => Multiply(x, Call("log", x));
    private static Formula Moment() => Call("productLogMoment", N("u"), N("v"));
    private static Formula MomentBody() => Subtract(Subtract(Subtract(Multiply(D(2), MulLog(L())),
        MulLog(N("u"))), MulLog(N("v"))),
        new Formula.Fraction(Add(MulLog(Root(true)), MulLog(Root(false))), D(2)));
    private static Formula KernelFunction() => Seq(LambdaLower, Sp, Par(Seq(N("s"), Colon, Sp, R())),
        Sp, Mapsto, Sp, Call("productLogKernel", N("u"), N("v"), N("s")));
    private static Formula PositiveHalfLine() => Seq(Open, D(0), Comma, Sp, Infty, Close);
    private static Formula Integral() => Seq(Int, Underscore, Grp(D(0)), Caret, Grp(Infty), Sp,
        Call("productLogKernel", N("u"), N("v"), N("s")), Sp, N("ds"));
}
