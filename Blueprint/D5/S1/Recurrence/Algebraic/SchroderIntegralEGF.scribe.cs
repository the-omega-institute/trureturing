using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class SchroderIntegralEGFDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/oeis2024a338193");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The EGF coefficients in OEIS A338193 equal Kurkov's two-index recurrence.",
        H("An Integral EGF And Schroeder Rows"),
        Blocks(
            FormulaNode("primitive", "Formal integral with zero constant coefficient", PrimitiveFormula(),
                "For a rational series S, the constant coefficient is zero and coefficient n at positive n is coeff(n-1,S)/n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            FormulaNode("primitive_zero", "The integral has zero constant coefficient",
                All("S", PS(), Equal(Call("constantCoeff", Call("primitive", V("S"))), D(0))),
                "The selected formal primitive has constant coefficient zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            FormulaNode("derivative_primitive", "Differentiation recovers the integrand",
                All("S", PS(), Equal(Call("derivative", Call("primitive", V("S"))), V("S"))),
                "Differentiating the zero-constant formal primitive recovers the rational series S.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Note("f", "Kurkov's recurrence",
                "Set f(j,0)=1. For positive m, the boundary is "
                + "f(0,m)=f(0,m-1)+m f(1,m-1). For positive j and m, use "
                + "f(j,m)=f(j-1,m)+m(f(j,m-1)+f(j+1,m-1)). "
                + "Recursion first decreases m, then j; all values are natural numbers.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("schroder-primitive"),
                DeclarationHandle.Create(Prefix + "primitive"), H("Formal primitive"),
                StatementSource.FromAuthor(PrimitiveFormula0()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The formal primitive divides the preceding coefficient by its positive degree and has constant coefficient zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("schroder-primitive-zero"),
                DeclarationHandle.Create(Prefix + "primitive_zero"), H("Zero constant coefficient"),
                StatementSource.FromAuthor(PrimitiveFormula1()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The primitive starts at zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("schroder-derivative-primitive"),
                DeclarationHandle.Create(Prefix + "derivative_primitive"), H("Derivative of the primitive"),
                StatementSource.FromAuthor(PrimitiveFormula2()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Differentiating cancels each positive degree denominator."))), DescribeRole.Theorem),
            Note("Original", "The original integral equation",
                "A has constant coefficient one and satisfies "
                + "A=1+Integral ((x/A)' / (x/A^2)') dx. Integration is formal, "
                + "with constant term zero, and all series have rational coefficients. "
                + "The inverse series and the derivative in the denominator have "
                + "constant coefficient one.", AssessedProvenance.FromLiterature(Source)),
            Note("original_exists_unique", "Existence and coefficient uniqueness",
                "Write F(j) for the EGF of row j. The recurrence gives "
                + "F(j+1)=F(j)+x(F(j+1)+F(j+2)). Mathlib's large Schroeder series "
                + "R satisfies R=1+xR+xR^2. Induction first on degree and then on j "
                + "proves F(j)=F(0)R^j. The boundary gives B'=F(0) for "
                + "B=F(0)(1-xR), and B has constant term one. Clearing the units "
                + "in the original equation gives (1+x)AA'-2x(A')^2-A^2=0. "
                + "Its constant-one branch is exactly (1-xR)A'=A: the alternative "
                + "factor has constant term minus one. Strong induction on coefficients "
                + "then proves uniqueness, canceling the nonzero rational factor n+1.",
                AssessedProvenance.FromRepo(Source)),
            Note("A", "The series specified by the source equation",
                "Choose the unique series satisfying Original. The selection predicate "
                + "contains only the original integral equation and initial value. "
                + "The recurrence and the coefficient identity are proved separately.",
                AssessedProvenance.FromRepo(Source)),
            Note("A_original", "The defining equation holds",
                "The chosen A satisfies the original integral equation and A(0)=1.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(DescribeId.Create("a338193-egf-coeff-eq-f"),
                DeclarationHandle.Create(Prefix + "egf_coeff_eq_f"),
                H("The coefficient identity"), StatementSource.FromAuthor(CoefficientIdentity()),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                "For every natural n at least one, n! times coefficient n of A equals "
                + "f(0,n-1), viewed in the rationals. Uniqueness identifies A with B; "
                + "differentiating shifts the EGF coefficient index by one, and "
                + "B'=F(0) completes the comparison. Thus the identity also proves "
                + "that every positive-index EGF coefficient is a natural number."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a338193-egf-coefficients"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock FormulaNode(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a338193-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula PS() => Call("PowerSeries", Rat());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula PrimitiveFormula()
    {
        var n = V("n"); var series = V("S");
        var body = Seq(V("if"), Sp, Parenthesized(Equal(n, D(0))), Sp, V("then"), Sp,
            D(0), Sp, V("else"), Sp, new Formula.Fraction(
                Call("coeff", Subtract(n, D(1)), series), Parenthesized(Seq(n, Colon, Sp, Rat()))));
        var lambda = Parenthesized(Seq(V("fun"), Sp, n, Colon, Sp, Nat(), Sp, Mapsto, Sp, body));
        return All("S", PS(), Equal(Call("primitive", series), Call("mk", lambda)));
    }

    private static Formula CoefficientIdentity() => Disp(Seq(
        Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        D(1), Sp, Le, Sp, F.Id("n"), Sp, Implies, Sp,
        F.Id("n"), Bang, Sp, OpenBracket, new Formula.Power(F.Id("x"), F.Id("n")),
        CloseBracket, F.Id("A"), Sp, Eq, Sp,
        new Formula.Apply(F.Id("f"), [D(0), Seq(F.Id("n"), Minus, D(1))])));

    private static DocumentBlock Note(string name, string title, string prose,
        AssessedProvenance provenance) => Describe.Remark(
        DescribeId.Create("a338193-" + (name == "A" ? "series-a" : name.ToLowerInvariant().Replace('_', '-'))),
        DeclarationHandle.Create(Prefix + name), H(title), provenance,
        Blocks(Paragraph(Text(prose))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula PrimitiveFormula0() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, F.Id("primitive"), Sp, F.Id("S"), Sp, Eq, Sp, Qualified("PowerSeries", "mk"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Mapsto, Sp, F.Id("if"), Sp, F.Id("n"), Sp, Eq, Sp, D(0), Sp, F.Id("then"), Sp, D(0), Sp, F.Id("else"), Sp, Qualified("PowerSeries", "coeff"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Minus, Sp, D(1))), Sp, F.Id("S"), Sp, Slash, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q")))))))));
    private static Formula PrimitiveFormula1() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Qualified("PowerSeries", "constantCoeff"), Sp, Parenthesized(Seq(F.Id("primitive"), Sp, F.Id("S"))), Sp, Eq, Sp, D(0)));
    private static Formula PrimitiveFormula2() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Qualified("PowerSeries", "derivative"), Sp, Parenthesized(Seq(F.Id("primitive"), Sp, F.Id("S"))), Sp, Eq, Sp, F.Id("S")));
}
