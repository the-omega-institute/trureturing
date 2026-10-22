using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class OverpartitionSquareLogDerivativeModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2012a219431");
    private const string NameQuotation =
        "Logarithmic derivative of the g.f. of the overpartitions of n^2 (A219430).";
    private const string SamplingQuotation =
        "Number of overpartitions of n^2; a(n) = A015128(n^2).";
    private const string ClaimQuotation =
        "Conjecture: a(2*n+1) == 2 (mod 4), a(2*n) == 0 (mod 4).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic derivative of square-indexed overpartitions has residue twice its index modulo four.",
        H("Hanna's Overpartition Logarithmic Derivative Modulo Four"),
        Blocks(
            Paragraph(Text("PowerSeries denotes formal power series. X is the indeterminate; "
                + "coeff extracts a coefficient, mk constructs a series from its coefficient function, "
                + "and derivative is PowerSeries.derivative. The product is a Finset product over "
                + "Finset.Icc 1 m. All series in the displayed definitions have rational coefficients. "
                + "The integer z is explicitly cast to Q in the coefficient equality. Int.ModEq "
                + "uses integer modulus four. OEIS A219431 has offset one.")),
            Node("pbar", "Overpartition coefficients", PbarFormula(),
                "OEIS A219430, unpaginated Name line: \"" + SamplingQuotation + "\" "
                + "A015128 counts overpartitions. Its generating function is the product of "
                + "(1 + X^k)/(1 - X^k) for positive k. At degree m, factors with k > m "
                + "cannot change the coefficient, giving the finite product displayed here.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("G", "The square-indexed generating function", GeneratingFormula(),
                "OEIS A219430, unpaginated Name line: \"" + SamplingQuotation + "\" "
                + "The natural index n is squared before pbar is evaluated, including n = 0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("logDerivative", "The logarithmic derivative", LogFormula(),
                "OEIS A219431, unpaginated Name line: \"" + NameQuotation + "\" "
                + "The series is X times the formal derivative of G times its inverse. "
                + "The factor X gives the entry's indexing starting at one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's congruences", Equal(Named("claim"), Parenthesized(ClaimBody())),
                "OEIS A219431, unpaginated Comment line: \"" + ClaimQuotation + "\" "
                + "For every natural m >= 1, one integer z equals the rational coefficient "
                + "and has residue two when m is odd and zero when m is even.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture holds", ClaimBody(),
                "Modulo four, the product of the overpartition factors equals one plus twice "
                + "the sum of their positive geometric tails: every term containing two factors "
                + "of two vanishes. Its degree-m coefficient is twice the divisor count. "
                + "A positive square has an odd divisor count, so G reduces to one plus twice "
                + "the series with every positive coefficient equal to one. Multiplication by "
                + "the inverse removes no further terms from twice its derivative modulo four, "
                + "giving coefficient 2m. The unit constant coefficient of the integer lift "
                + "ensures that the logarithmic derivative has integer coefficients.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a219431-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(Formula name, params Formula[] arguments) => new Formula.Apply(name, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call(Named("PowerSeries"), Rationals());
    private static Formula Forall(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Inverse(Formula value) => Power(Parenthesized(value), Seq(Minus, D(1)));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula PbarFormula()
    {
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula xk = Power(F.Id("X"), k);
        Formula unit = Parenthesized(Seq(D(1), Colon, Sp, Series()));
        Formula factor = Mul(Parenthesized(Add(D(1), xk)), Inverse(Subtract(unit, xk)));
        Formula product = Seq(new Formula.Subscript(F.Prod,
            Seq(k, Sp, InMacro, Sp, Call(Qualified("Finset", "Icc"), D(1), m))), Sp,
            Parenthesized(factor));
        return Forall("m", Naturals(), Equal(Call(Named("pbar"), m),
            Call(Named("coeff"), m, Parenthesized(product))));
    }

    private static Formula GeneratingFormula()
    {
        Formula n = F.Id("n");
        Formula coefficient = Call(Named("pbar"), Power(n, D(2)));
        Formula function = Parenthesized(Seq(Named("fun"), Sp, n, Colon, Sp, Naturals(), Sp,
            Mapsto, Sp, coefficient));
        return Equal(Named("G"), Call(Named("mk"), function));
    }

    private static Formula LogFormula() => Equal(Named("logDerivative"),
        Mul(Mul(F.Id("X"), Call(Named("derivative"), Named("G"))), Inverse(Named("G"))));

    private static Formula ClaimBody()
    {
        Formula m = F.Id("m");
        Formula z = F.Id("z");
        Formula cast = Parenthesized(Seq(z, Colon, Sp, Rationals()));
        Formula coefficient = Equal(Call(Named("coeff"), m, Named("logDerivative")), cast);
        Formula odd = Implies(Call(Named("Odd"), m),
            Call(Qualified("Int", "ModEq"), D(4), z, D(2)));
        Formula even = Implies(Call(Named("Even"), m),
            Call(Qualified("Int", "ModEq"), D(4), z, D(0)));
        return Forall("m", Naturals(), Implies(Leq(D(1), m),
            Exists("z", Integers(), And(coefficient, And(odd, even)))));
    }
}
