using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaSquareCompositionModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2024a372527");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral power-series solution has residue two modulo four exactly at shifted powers of two above degree one.",
        H("Hanna's Square-Composition Congruence"),
        Blocks(
            Paragraph(Text("PowerSeries denotes formal power series, X is the indeterminate, "
                + "coeff(n,A) is coefficient n, and constantCoeff(A) is the constant coefficient. "
                + "The argument order subst(g,A) is Mathlib's PowerSeries.subst: it means A(g). "
                + "The inverse is the inverse in the power-series ring. Rational coefficients "
                + "are compared with integers through the displayed rational coercion. "
                + "Int.ModEq(4,m,r) means that the integers m and r are congruent modulo four.")),
            Node("IsGF", "The normalized generating equation", IsGFFormula(),
                "The Name of the unpaginated OEIS A372527 entry reads: "
                + "\"Expansion of g.f. A(x) satisfying A( A(x)^2 ) = x*A(x)/(1 - 2*A(x)).\" "
                + "The series has rational coefficients, zero constant coefficient, and linear "
                + "coefficient one, as specified by the entry's offset-one data. "
                + "The denominator has constant coefficient one and is therefore a unit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The residue proposition", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "The Comments of the unpaginated OEIS A372527 entry state: "
                + "\"Conjecture: a(2^k + 1) == 2 (mod 4) for k >= 0, and a(n) == 0 (mod 4) "
                + "for n > 0 when n is not of the form 2^k + 1.\" "
                + "Here a(n) is coeff(n,A), the integers k and n used as indices are natural numbers, "
                + "and the integer m equals the indicated rational coefficient. "
                + "The second clause is restricted to n greater than one because the entry's "
                + "first term is a(1)=1. The proposition also asserts existence of a normalized solution.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The A372527 congruence theorem", Disp(ClaimBody()),
                "Write A=X*B. The cleared equation becomes "
                + "B*(1-2*X*B)*subst(X squared*B squared,B)=1. "
                + "Taking the inverse of the last two factors defines a transformation that "
                + "improves agreement by one degree among series with constant coefficient one. "
                + "Its iterates have stable integer coefficients and give a unique solution over "
                + "each commutative ring. In ZMod(4), double the coefficients of the power-of-two "
                + "series over ZMod(2). The resulting series d satisfies 2*d=0, d squared=0, "
                + "and subst(X squared,d)=d-2*X. Thus X*(1+d) satisfies the cleared equation. "
                + "Uniqueness identifies it with the reduction of the integer solution. "
                + "Its coefficient at every degree above one is two exactly at a shifted power of two, "
                + "and zero elsewhere. Rational uniqueness then gives the assertion for every normalized solution.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna-a372527-square-composition-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("hanna-square-mod-four-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
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
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula X() => F.Id("X");
    private static Formula ShiftedPower(Formula k) => Add(Pow(D(2), k), D(1));
    private static Formula IsGFFormula()
    {
        Formula a = F.Id("A");
        return Disp(Seq(Bound("A", Series()), Equal(Call("IsGF", a), Parenthesized(And(
            Equal(Call("constantCoeff", a), D(0)), And(Equal(Call("coeff", D(1), a), D(1)),
                Equal(Call("subst", Pow(a, D(2)), a),
                    Mul(Mul(X(), a), Pow(Sub(D(1), Mul(D(2), a)), Seq(Minus, D(1)))))))))));
    }
    private static Formula IntegerCoefficient(Formula a, Formula index, Formula residue)
    {
        Formula m = F.Id("m");
        return Exist("m", Integers(), And(
            Equal(Call("coeff", index, a), Parenthesized(Seq(m, Colon, Sp, Rationals()))),
            new Formula.Apply(Qualified("Int", "ModEq"), [D(4), m, residue])));
    }
    private static Formula ClaimBody()
    {
        Formula a = F.Id("A"), k = F.Id("k"), n = F.Id("n");
        Formula exists = Exist("A", Series(), Call("IsGF", a));
        Formula dyadic = Seq(Bound("k", Naturals()), IntegerCoefficient(a, ShiftedPower(k), D(2)));
        Formula other = Seq(Bound("n", Naturals()), ImpliesTo(Seq(D(1), Sp, Lt, Sp, n),
            ImpliesTo(Seq(Neg, Sp, Parenthesized(Exist("k", Naturals(), Equal(n, ShiftedPower(k))))),
                IntegerCoefficient(a, n, D(0)))));
        return And(exists, Seq(Bound("A", Series()), ImpliesTo(Call("IsGF", a), And(dyadic, other))));
    }
}
