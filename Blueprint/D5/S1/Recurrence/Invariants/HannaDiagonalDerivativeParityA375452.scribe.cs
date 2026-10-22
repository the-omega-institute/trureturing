using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaDiagonalDerivativeParityA375452Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2024a375449a375452");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The diagonal derivative equation has integral coefficients, with odd coefficients at exactly two Mersenne supports above degree one.",
        H("Hanna's A375452 Diagonal Derivative Parity"),
        Blocks(
            Paragraph(Text("PowerSeries denotes formal power series over the rational numbers. "
                + "The symbol X is the indeterminate, derivative is the formal derivative, "
                + "coeff extracts a coefficient, and C embeds a scalar as a constant series. "
                + "The inverse is taken in the formal power-series ring; the denominator has constant coefficient one. "
                + "Indices and powers are natural numbers, and subtraction in the support indices is natural subtraction. "
                + "The displayed rational coercion identifies each coefficient with an integer m.")),
            Node("IsGF", "The normalized generating equation", IsGFFormula(),
                "The Name field of the unpaginated OEIS A375452 entry states: "
                + "\"Expansion of g.f. A(x) satisfying [x^n] x*A'(x) / (1 - n*A(x)) = n^n for n >= 1.\" "
                + "The offset is one, encoded by zero constant coefficient. "
                + "The scalar n in C is a rational number.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The coefficient parity proposition", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "The Comments field of the unpaginated OEIS A375452 entry states: "
                + "\"Conjecture: for n > 1, a(n) is odd iff n is of the form 2^k-2 or 2^k-1 for some k > 1.\" "
                + "Here a(n) is coefficient n of any normalized rational solution. "
                + "The proposition also states existence and integrality of the indicated coefficients.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The A375452 parity theorem", Disp(ClaimBody()),
                "The integer forcing sequence is "
                + "n^(n-1). "
                + "For every positive n its residue modulo two equals that of n. "
                + "The shared diagonal recursion constructs an integral solution. "
                + "Over ZMod(2), its reduction is the sum of the Mersenne series T and T squared. "
                + "The two summands have odd and even support respectively, which gives the equivalence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a375452-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Exist(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula ImpliesTo(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Positive(Formula value) => Seq(D(1), Sp, Le, Sp, value);
    private static Formula AboveOne(Formula value) => Seq(D(1), Sp, Lt, Sp, value);
    private static Formula DiagonalCoefficient(Formula a, Formula n) =>
        Call("coeff", n, Mul(Mul(F.Id("X"), Call("derivative", a)),
            Pow(Sub(D(1), Mul(Call("C", Cast(n, Rationals())), a)), Seq(Minus, D(1)))));
    private static Formula CoefficientParity(Formula a, Formula n)
    {
        Formula m = F.Id("m"), k = F.Id("k");
        Formula support = Exist("k", Naturals(), And(AboveOne(k),
            Seq(Parenthesized(Equal(n, Sub(Pow(D(2), k), D(2)))), Sp, Lor, Sp,
                Parenthesized(Equal(n, Sub(Pow(D(2), k), D(1)))))));
        return Exist("m", Integers(), And(Equal(Call("coeff", n, a), Cast(m, Rationals())),
            Seq(Parenthesized(Call("Odd", m)), Sp, Iff, Sp, Parenthesized(support))));
    }

    private static Formula IsGFFormula()
    {
        Formula a = F.Id("A"), n = F.Id("n");
        Formula coefficients = Seq(Bound("n", Naturals()), ImpliesTo(Positive(n),
            Equal(DiagonalCoefficient(a, n), Pow(Cast(n, Rationals()), n))));
        Formula body = And(Equal(Call("constantCoeff", a), D(0)), coefficients);
        return Disp(Seq(Bound("A", Series()), Equal(Call("IsGF", a), Parenthesized(body))));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("A"), n = F.Id("n");
        return And(Exist("A", Series(), Call("IsGF", a)),
            Seq(Bound("A", Series()), ImpliesTo(Call("IsGF", a),
                Seq(Bound("n", Naturals()), ImpliesTo(AboveOne(n), CoefficientParity(a, n))))));
    }
}
