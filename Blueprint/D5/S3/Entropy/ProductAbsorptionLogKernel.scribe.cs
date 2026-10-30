using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class ProductAbsorptionLogKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/ProductAbsorptionLogKernel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/local2026productabsorption");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact five-term logarithmic kernel for binary product absorption has at most one positive sign change, from positive to negative.",
        H("The Product Absorption Logarithmic Kernel"),
        Blocks(
            Paragraph(Text("Let u and v belong to the closed unit interval. Put A=u+v, B=uv, L=A-B, "
                + "and Mplus=A-2B+2sqrt(B(1-A+B)), Mminus=A-2B-2sqrt(B(1-A+B)). "
                + "Both roots are nonnegative, their sum is 2(A-2B), and their product is (u-v)^2. "
                + "In particular u=v is permitted and gives Mminus=0. Every logarithm in the kernel has a strictly positive argument when s>0.")),
            Node("productLogKernel", "The exact logarithmic kernel", DescribeRole.Definition,
                AllReal("u", AllReal("v", AllReal("s", Equal(K(N("s")), KernelBody())))),
                "The definition is a total real function. Its single-crossing theorem concerns 0<=u,v<=1 and s>0. "
                + "The logarithm is the natural logarithm. A zero quadratic root contributes log(1)=0."),
            Node("product_log_kernel_single_crossing", "One positive sign change", DescribeRole.Theorem,
                Statement(),
                "Either K is nonnegative for every positive s, or there exists a positive r with K(r)=0, "
                + "K(s)>0 for every 0<s<r, and K(s)<0 for every s>r. The strict signs make the zero unique in the second case. "
                + "There is no assumption that u and v are unequal, and all parameter endpoints are included."),
            Paragraph(Text("Twice the kernel is log(N)-log(D), where "
                + "N=(s^2+As+B)^2(s^2+2(A-2B)s+A^2-4B) and D=s^2(s+A-B)^4. "
                + "Both N and D are positive. Their difference is the quartic "
                + "P(s)=aFour*s^4+aThree*s^3+aTwo*s^2+aOne*s+aZero. The coefficients are "
                + "aFour=2B(2A-3B-1), aThree=2B(4A^2-6AB-A+2B^2-4B), "
                + "aTwo=B(4A^3-6A^2B+2A^2+4AB^2-8AB-B^3-7B), "
                + "aOne=2B(A^3-3AB-2B^2), and aZero=B^2(A^2-4B).")),
            Paragraph(Text("For 0<u,v<1 the coefficient estimates give aZero>=0, aOne>0, aTwo>0, "
                + "and aFour>=0 implies aThree>=0. In the latter case P is nonnegative. "
                + "When aFour<0 and aThree>=0, P(s)/s^4 is strictly decreasing. "
                + "When both aFour and aThree are negative, P(s)/s^3 is strictly decreasing. "
                + "Continuity and the signs at small and large positive arguments give the unique crossing. "
                + "The strict monotonicity of log transfers its signs to the original five-term kernel.")),
            Paragraph(Text("At u=0 the kernel vanishes identically. At u=1 it is "
                + "log(1+v/s)+log(1+(1-v)/s)-log(1+1/s), which is nonnegative because "
                + "(1+v/s)(1+(1-v)/s)-(1+1/s)=v(1-v)/s^2>=0. "
                + "Symmetry supplies the two remaining boundary faces. Thus no strict positivity of u, v, or a quadratic root is required.")),
            Paragraph(Text("This is the kernel crossing component of the scalar binary-entropy absorption argument. "
                + "The entropy integral representation, absolute integrability, the nonnegative first moment, "
                + "the decreasing-weight integral argument, and the closed-domain entropy inequality are separate mathematical statements. "
                + "No spectral-entropy, quantum-channel, or all-product-seed absorption conclusion is asserted by this theorem. "
                + "The ordinary mathematical source is the local unpublished proof identified in the source note; no publication-priority claim is made.")))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("product-absorption-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static Formula N(string name) => F.Id(name);
    private static Formula R() => Seq(Mathbb, Grp(N("R")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula AllReal(string name, Formula body) => Seq(Forall, Sp,
        Par(Seq(N(name), Colon, Sp, R())), Comma, Sp, body);
    private static Formula ExistsReal(string name, Formula body) => Seq(Exists, Sp,
        Par(Seq(N(name), Colon, Sp, R())), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Inside(Formula x) => And(Le(D(0), x), Le(x, D(1)));
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula A() => Add(N("u"), N("v"));
    private static Formula B() => Multiply(N("u"), N("v"));
    private static Formula L() => Subtract(A(), B());
    private static Formula Q() => Call("sqrt", Multiply(B(), Add(Subtract(D(1), A()), B())));
    private static Formula Root(bool plus) => plus
        ? Add(Subtract(A(), Multiply(D(2), B())), Multiply(D(2), Q()))
        : Subtract(Subtract(A(), Multiply(D(2), B())), Multiply(D(2), Q()));
    private static Formula LogTerm(Formula x) => Call("log", Add(D(1), Frac(x, N("s"))));
    private static Formula K(Formula s) => Call("productLogKernel", N("u"), N("v"), s);
    private static Formula Nonnegative() => AllReal("s", Imp(Lt(D(0), N("s")), Le(D(0), K(N("s")))));
    private static Formula Before() => AllReal("s", Imp(And(Lt(D(0), N("s")), Lt(N("s"), N("r"))),
        Lt(D(0), K(N("s")))));
    private static Formula After() => AllReal("s", Imp(Lt(N("r"), N("s")), Lt(K(N("s")), D(0))));
    private static Formula Crossing() => ExistsReal("r", And(Lt(D(0), N("r")),
        And(Equal(K(N("r")), D(0)), And(Before(), After()))));
    private static Formula Statement() => AllReal("u", AllReal("v", Imp(Inside(N("u")),
        Imp(Inside(N("v")), Or(Nonnegative(), Crossing())))));
    private static Formula KernelBody() => Add(
        Subtract(Add(LogTerm(N("u")), LogTerm(N("v"))), Multiply(D(2), LogTerm(L()))),
        Frac(Add(LogTerm(Root(true)), LogTerm(Root(false))), D(2)));
}
