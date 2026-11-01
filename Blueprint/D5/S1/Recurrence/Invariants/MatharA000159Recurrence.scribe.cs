using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class MatharA000159RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/MatharA000159Recurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/mathar2015a000159");
    private const string RecurrenceQuote =
        "Conjecture: 2*(-252307*n + 1041077)*a(n) + (504614*n^2 - 3362985*n + 5118150)*a(n-1) + "
        + "(1280831*n^2 - 7397886*n + 6461565)*a(n-2) + (746598*n^2 - 2913543*n - 1336090)*a(n-3) + "
        + "(-405481*n^2 + 6175011*n - 15469320)*a(n-4) + (-375862*n^2 + 4098537*n - 8846430)*a(n-5) + "
        + "2*(-187931*n + 560630)*a(n-6) = 0.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-hit ménage coefficients satisfy Mathar's six-step recurrence.",
        H("Mathar's Six-Step Recurrence for Three-Hit Ménage Numbers"),
        Blocks(
            Paragraph(Text("U is a polynomial over the rational numbers. Polynomial.C embeds a rational "
                + "as a constant polynomial, Polynomial.X is the indeterminate, and Polynomial.coeff extracts a coefficient. "
                + "All indices are natural numbers. Subtractions in indices, factorial arguments and binomial arguments "
                + "are natural subtraction; the sum has k at most n, so these subtractions agree with integer subtraction. "
                + "The quotients and displayed casts have values in the rational numbers. "
                + "For n positive every summand denominator is at least n. The recurrence uses n at least nine, "
                + "so each sequence argument is at least three.")),
            Node("U", "The ménage hit polynomial", UFormula(),
                "The unpaginated OEIS A058087 FORMULA field states: "
                + "\"Row n of the triangle lists the coefficients of the polynomial U_n(t) = Sum_{k=0..n} "
                + "(2*n/(2*n-k))*binomial(2*n-k,k)*(n-k)!*(t-1)^k, with higher order terms first "
                + "(Kaplansky and Riordan).\" Its Maple definition begins "
                + "\"U := proc(n) if n = 0 then return 1 fi;\". "
                + "U uses this constant branch at zero and the quoted finite sum at positive n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The three-hit coefficient", AFormula(),
                "The unpaginated OEIS A000159 NAME field states: \"a(n) = A058087(n,n-3).\" "
                + "The A058087 NAME field states: \"Triangle read by rows, giving coefficients of the ménage hit "
                + "polynomials ordered by descending powers. T(n, k) for 0 <= k <= n.\" "
                + "Thus a(n) is the coefficient of degree three in U(n). The source offset is 3,1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The six-step recurrence proposition",
                Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "The unpaginated OEIS A000159 first FORMULA field states: \"" + RecurrenceQuote
                + "\" — R. J. Mathar, Nov 02 2015. The quantifier ranges over every natural n at least nine, "
                + "the first index whose six backward shifts all belong to the sequence's domain.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The recurrence holds at every source-domain index", Disp(ClaimBody()),
                "Coefficient extraction converts the rook sum into a rational affine expression in the "
                + "factorial series evaluated at X/(1+X)^2. The factorial series satisfies a first-order formal "
                + "differential equation. After differentiating and clearing denominators, the resulting "
                + "second-order equation has polynomial forcing of degree five. Its coefficient at n at least "
                + "nine is exactly the displayed recurrence. The argument uses formal power series and "
                + "does not require convergence or an inverse of the indeterminate.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("mathar-a000159-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Rationals()));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Minus(Formula value) => Seq(F.Minus, value);
    private static Formula Number(long value) => new Formula.Number(value);

    private static Formula UFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula twice = Mul(D(2), n), difference = Sub(twice, k);
        Formula scalar = Mul(Mul(new Formula.Fraction(Cast(twice), Cast(difference)),
            Cast(App(Qualified("Nat", "choose"), difference, k))),
            Cast(App(Qualified("Nat", "factorial"), Sub(n, k))));
        Formula summand = Mul(App(Qualified("Polynomial", "C"), scalar),
            Pow(Sub(Qualified("Polynomial", "X"), D(1)), k));
        Formula range = App(Qualified("Finset", "range"), Add(n, D(1)));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Seq(k, Sp, InMacro, Sp, range)), Sp, summand);
        Formula body = Call("ite", Equal(n, D(0)), D(1), sum);
        return Disp(Seq(Bound("n", Naturals()), Equal(Call("U", n), body)));
    }

    private static Formula AFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()), Equal(Call("a", n),
            App(Qualified("Polynomial", "coeff"), Call("U", n), D(3)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), x = Cast(n);
        Formula Term(Formula coefficient, Formula shift) =>
            Mul(Parenthesized(coefficient), Call("a", shift));
        Formula Quadratic(long square, long linear, long constant)
        {
            Formula first = square < 0 ? Minus(Mul(Number(-square), Pow(x, D(2))))
                : Mul(Number(square), Pow(x, D(2)));
            Formula second = linear < 0 ? Sub(first, Mul(Number(-linear), x))
                : Add(first, Mul(Number(linear), x));
            return constant < 0 ? Sub(second, Number(-constant)) : Add(second, Number(constant));
        }
        Formula[] rows = [
            Term(Mul(D(2), Parenthesized(Add(Minus(Mul(Number(252307), x)), Number(1041077)))), n),
            Seq(Plus, Term(Quadratic(504614, -3362985, 5118150), Sub(n, D(1)))),
            Seq(Plus, Term(Quadratic(1280831, -7397886, 6461565), Sub(n, D(2)))),
            Seq(Plus, Term(Quadratic(746598, -2913543, -1336090), Sub(n, D(3)))),
            Seq(Plus, Term(Quadratic(-405481, 6175011, -15469320), Sub(n, D(4)))),
            Seq(Plus, Term(Quadratic(-375862, 4098537, -8846430), Sub(n, D(5)))),
            Seq(Plus, Term(Mul(D(2), Parenthesized(Add(Minus(Mul(Number(187931), x)), Number(560630)))), Sub(n, D(6)))),
            Seq(Eq, Sp, D(0))
        ];
        return Seq(Bound("n", Naturals()), D(9), Sp, Le, Sp, n, Sp, Implies, Sp,
            new Formula.Aligned([.. rows]));
    }
}
