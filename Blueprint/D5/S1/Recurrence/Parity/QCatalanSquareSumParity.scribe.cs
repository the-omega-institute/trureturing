using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class QCatalanSquareSumParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/QCatalanSquareSumParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2024a376527");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square sum of a Carlitz-Riordan q-Catalan row is odd exactly one below a power of two.",
        H("q-Catalan Row Square-Sum Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2024a376527 defines a(n) as the sum "
                + "of the squared coefficients in row n of the Carlitz-Riordan q-Catalan "
                + "triangle. It asks whether the odd rows are exactly those indexed by "
                + "2^k-1.")),
            Paragraph(Text("All indices are natural numbers. The row polynomials and their "
                + "coefficients are integer-valued. Write R(n) for qCatalanRow(n), T(n,k) "
                + "for qCatalanCoeff(n,k), S(n) for rowSum(n), a(n) for squareSum(n), and "
                + "C for the shifted integer Catalan series. The operator coeff extracts a "
                + "coefficient, eval evaluates a polynomial, and monomial(i,1) is q^i.")),
            Paragraph(Text("The map pi is Int.castRingHom into ZMod(2). Polynomial rows "
                + "avoid any need for a bivariate formal-series interface. Their degree "
                + "bound makes the displayed finite square sum exactly the full row.")),
            Node("qCatalanRow", "The q-Catalan row polynomials", RowDefinition(),
                "The recursion is obtained by comparing the coefficient of x^(n+1) in "
                + "A(x,q)=1+x A(qx,q) A(x,q).", DescribeRole.Definition),
            Node("qCatalanCoeff", "The q-Catalan coefficient triangle", CoefficientDefinition(),
                "The triangle entry T(n,k) is coefficient k of the row polynomial R(n).",
                DescribeRole.Definition),
            Node("rowSum", "The row sum", RowSumDefinition(),
                "Evaluation at q=1 adds all coefficients of the row polynomial.",
                DescribeRole.Definition),
            Node("squareSum", "The finite square sum", SquareSumDefinition(),
                "The upper index n(n-1)/2 is the degree bound for the nth row.",
                DescribeRole.Definition),
            Node("qCatalanRow_succ", "Coefficient-extracted row recurrence", RowRecurrence(),
                "Each split i+(n-i)=n contributes q^i R(i) R(n-i)."),
            Node("rowSum_eq_catalan", "Specialization at q=1", RowSumCatalan(),
                "At q=1 the powers q^i disappear, so S obeys the Catalan convolution. "
                + "The series X times the generating series of S has zero constant "
                + "coefficient and satisfies F=X+F^2. Catalan uniqueness identifies it "
                + "with C, including the one-place coefficient shift."),
            Node("squareSum_mod_two_eq_catalan", "Square sums modulo two", SquareSumParity(),
                "Every element u of ZMod(2) satisfies u^2=u. Summing this identity across "
                + "the finite row identifies the reduced square sum with the reduced row "
                + "sum, hence with the corresponding coefficient of C."),
            Node("hanna_conjecture", "Hanna's A376527 parity conjecture", HannaFormula(),
                "The binary Catalan theorem says that coefficient n+1 of C is one exactly "
                + "when n+1=2^k. Positivity of powers of two makes this equivalent to "
                + "n=2^k-1, including n=0 at k=0.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a376527-q-catalan-square-sum-parity"),
                    ResolutionKind.Proved))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity"))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a376527-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Row(Formula n) => Call("R", n);
    private static Formula Entry(Formula n, Formula k) => Call("T", n, k);
    private static Formula RowTotal(Formula n) => Call("S", n);
    private static Formula SquareTotal(Formula n) => Call("a", n);
    private static Formula Catalan() => F.Id("C");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Reduce(Formula value) => Call("pi", value);

    private static Formula RowTerm(Formula n, Formula i) => Mul(
        Mul(Call("monomial", i, D(1)), Row(i)), Row(Sub(n, i)));

    private static Formula RowRecurrenceBody()
    {
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula sum = Seq(new Formula.Subscript(F.Sum,
            Seq(i, Sp, InMacro, Sp, Call("Fin", Add(n, D(1))))), Sp,
            Parenthesized(RowTerm(n, i)));
        return new Formula.Aligned([
            Equal(Row(D(0)), D(1)),
            Seq(Bound("n", Naturals()), Equal(Row(Add(n, D(1))), sum))
        ]);
    }

    private static Formula RowDefinition() => Disp(RowRecurrenceBody());

    private static Formula CoefficientDefinition()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        return Disp(Seq(Bound("n", Naturals()), Bound("k", Naturals()),
            Equal(Entry(n, k), Call("coeff", k, Row(n)))));
    }

    private static Formula RowSumDefinition()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()),
            Equal(RowTotal(n), Call("eval", D(1), Row(n)))));
    }

    private static Formula Triangle(Formula n) =>
        Div(Mul(n, Parenthesized(Sub(n, D(1)))), D(2));

    private static Formula SquareSumDefinition()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp,
            Call("range", Add(Triangle(n), D(1))))), Sp, Power(Entry(n, k), D(2)));
        return Disp(Seq(Bound("n", Naturals()), Equal(SquareTotal(n), sum)));
    }

    private static Formula RowRecurrence()
    {
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula sum = Seq(new Formula.Subscript(F.Sum,
            Seq(i, Sp, InMacro, Sp, Call("Fin", Add(n, D(1))))), Sp,
            Parenthesized(RowTerm(n, i)));
        return Disp(Seq(Bound("n", Naturals()), Equal(Row(Add(n, D(1))), sum)));
    }

    private static Formula RowSumCatalan()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()), Equal(RowTotal(n),
            Call("coeff", Add(n, D(1)), Catalan()))));
    }

    private static Formula SquareSumParity()
    {
        Formula n = F.Id("n");
        Formula reducedCatalan = Call("map", F.Id("pi"), Catalan());
        return Disp(Seq(Bound("n", Naturals()), Equal(Reduce(SquareTotal(n)),
            Call("coeff", Add(n, D(1)), reducedCatalan))));
    }

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula support = Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Equal(n, Sub(Power(D(2), k), D(1))));
        return Disp(Seq(Bound("n", Naturals()), Call("Odd", SquareTotal(n)),
            Sp, Iff, Sp, Parenthesized(support)));
    }
}
