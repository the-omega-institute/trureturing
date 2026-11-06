using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class KurkovConvolutionRowRecursionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/kurkov2025a340991");
    private const string CoefficientQuote =
        "T(n,k) = [x^n] (Sum_{j>=1} prime(j)*x^j)^k.";
    private const string ConjectureQuote =
        "Conjecture: row polynomials are x*R(n,1) for n > 0 where "
        + "R(n,k) = R(n-1,k+1) + x*R(n-1,1)*R(1,k) for n > 1, k > 0 "
        + "with R(1,k) = prime(k) for k > 0. The same recursion seems to work "
        + "for self-convolution of any other sequence. - _Mikhail Kurkov_, Apr 05 2025";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kurkov's shifted array gives every positive convolution-row polynomial over a commutative semiring.",
        H("Kurkov's universal convolution-row recursion"),
        Blocks(
            Paragraph(Text(
                "The coefficient semiring K is arbitrary. Natural indices include zero, "
                + "but the sequence contributes only at positive indices. PowerSeries.X "
                + "is the series variable, and Polynomial.X is the polynomial variable. "
                + "The entry OEIS A340991 is unpaginated; the quotations below are its "
                + "FORMULA lines in revision 24.")),
            Node("sourceSeries", "The source series", SourceFormula(),
                CoefficientQuote + " The coefficient sequence prime(j) is replaced by "
                + "an arbitrary a. PowerSeries.mk assigns coefficient zero at j=0 "
                + "and coefficient a(j) at every positive j.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSeries", "Equality with the source series", SourcePredicateFormula(),
                "A is the source series exactly when it equals sourceSeries(a).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("T", "The convolution coefficient triangle", TriangleFormula(),
                CoefficientQuote + " The degree n coefficient of A raised to r is "
                + "the triangle entry T(A,n,r). The zeroth power is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rowPolynomial", "The finite row polynomial", RowFormula(),
                "The row polynomial has coefficient T(A,n,r) at power r for "
                + "r=0,...,n. The range n+1 includes both endpoints.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("kurkovR", "Kurkov's shifted polynomial array", ArrayFormula(),
                ConjectureQuote + " Positive columns start with C(a(k)). "
                + "Row zero and column zero are zero. In the successor equation "
                + "n and k range over all natural numbers. Commutativity allows "
                + "the product order X*C(a(k+1))*kurkovR(a,n+1,1).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The universal row identity", ClaimFormula(),
                ConjectureQuote + " For every commutative semiring and sequence, "
                + "there exists its zero-constant source series, and every row "
                + "with 1<=n equals Polynomial.X times column one of kurkovR. "
                + "Row zero is outside the asserted identity; a(0) does not occur.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The universal convolution-row recursion", ClaimBody(),
                "Splitting the coefficient tail into its constant term and "
                + "PowerSeries.X times the next tail reproduces the two summands "
                + "of kurkovR. Induction identifies each positive array column "
                + "coefficient with a coefficient of a source-series power times "
                + "that tail. Coefficients below the power vanish, giving the "
                + "finite row polynomial. No positivity, nonzero coefficient, "
                + "division, or characteristic assumption is required.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("a340991-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula OverSemiring(Formula body) =>
        All("K", Named("Type"), Seq(OpenBracket, Call("CommSemiring", F.Id("K")),
            CloseBracket, Sp, body));
    private static Formula OverSequence(Formula body) =>
        OverSemiring(All("a", Arrow(Naturals(), F.Id("K")), body));
    private static Formula SeriesType() => Call("PowerSeries", F.Id("K"));

    private static Formula SourceFormula()
    {
        Formula a = F.Id("a"), j = F.Id("j");
        Formula coefficients = Seq(Named("fun"), Sp, j, Colon, Sp, Naturals(), Sp,
            Mapsto, Sp, Named("if"), Sp, Equal(j, D(0)), Sp, Named("then"), Sp,
            D(0), Sp, Named("else"), Sp, App(a, j));
        return OverSequence(Equal(Call("sourceSeries", a),
            App(Qualified("PowerSeries", "mk"), coefficients)));
    }

    private static Formula SourcePredicateFormula()
    {
        Formula a = F.Id("a"), series = F.Id("A");
        return OverSequence(All("A", SeriesType(),
            new Formula.Logic(Call("IsSourceSeries", a, series), FormulaLogicOperator.Iff,
                Equal(series, Call("sourceSeries", a)))));
    }

    private static Formula TriangleFormula()
    {
        Formula series = F.Id("A"), n = F.Id("n"), r = F.Id("r");
        return OverSemiring(All("A", SeriesType(), All("n", Naturals(), All("r", Naturals(),
            Equal(Call("T", series, n, r),
                App(Qualified("PowerSeries", "coeff"), n, Power(series, r)))))));
    }

    private static Formula RowFormula()
    {
        Formula series = F.Id("A"), n = F.Id("n"), r = F.Id("r");
        Formula summand = Multiply(App(Qualified("Polynomial", "C"), Call("T", series, n, r)),
            Power(Qualified("Polynomial", "X"), r));
        Formula sum = Seq(new Formula.Subscript(F.Sum,
            Seq(r, Sp, InMacro, Sp, App(Qualified("Finset", "range"), Add(n, D(1))))),
            Sp, Parenthesized(summand));
        return OverSemiring(All("A", SeriesType(), All("n", Naturals(),
            Equal(Call("rowPolynomial", series, n), sum))));
    }

    private static Formula ArrayFormula()
    {
        Formula a = F.Id("a"), n = F.Id("n"), k = F.Id("k");
        Formula successor = Add(n, D(1)), column = Add(k, D(1));
        Formula rhs = Add(Call("kurkovR", a, successor, Add(k, D(2))),
            Multiply(Multiply(Qualified("Polynomial", "X"),
                App(Qualified("Polynomial", "C"), App(a, column))),
                Call("kurkovR", a, successor, D(1))));
        return OverSequence(new Formula.Aligned([
            All("k", Naturals(), Equal(Call("kurkovR", a, D(0), k), D(0))),
            Equal(Call("kurkovR", a, D(1), D(0)), D(0)),
            All("k", Naturals(), Equal(Call("kurkovR", a, D(1), column),
                App(Qualified("Polynomial", "C"), App(a, column)))),
            All("n", Naturals(), Equal(Call("kurkovR", a, Add(n, D(2)), D(0)), D(0))),
            All("n", Naturals(), All("k", Naturals(),
                Equal(Call("kurkovR", a, Add(n, D(2)), column), rhs))),
        ]));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("a"), series = F.Id("A"), n = F.Id("n");
        Formula positive = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n);
        Formula row = Equal(Call("rowPolynomial", series, n),
            Multiply(Qualified("Polynomial", "X"), Call("kurkovR", a, n, D(1))));
        return OverSequence(Some("A", SeriesType(),
            new Formula.Logic(
                Parenthesized(Call("IsSourceSeries", a, series)),
                FormulaLogicOperator.And,
                Parenthesized(All("n", Naturals(),
                    new Formula.Logic(positive, FormulaLogicOperator.Implies, row))))));
    }

    private static Formula ClaimFormula() =>
        new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, ClaimBody());
}
