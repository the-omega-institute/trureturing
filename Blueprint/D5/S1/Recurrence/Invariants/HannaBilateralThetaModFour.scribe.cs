using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaBilateralThetaModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a380060");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A380060 equation has an integral solution with residue two exactly at positive squares.",
        H("Hanna Bilateral Theta Congruence Modulo Four"),
        Blocks(
            Paragraph(Text("Paul D. Hanna, OEIS A380060, Name: \"G.f. A(x) satisfies A(x) = Sum_{n=-oo..+oo} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n.\" "
                + "Comments: \"The term x^(n^2) * (A - x^n)^n/(1 - x^n*A)^n is invariant under sign reversal of n.\" "
                + "Formula (2): \"A(x) = 1 + 2*Sum_{n>=1} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n.\" "
                + "These are the Name, Comments and Formula sections of the unpaginated entry.")),
            Paragraph(Text("PowerSeries(Q) denotes rational formal power series. The term of index zero is one, and the terms at opposite indices coincide. "
                + "IsGF uses formula (2), with the coefficient at degree m evaluated from the finite interval 1 through m. "
                + "A summand of index n contains X^(n^2), so larger indices contribute zero. "
                + "The inverse is the formal power-series inverse; each denominator has constant coefficient one. "
                + "All exponents and coefficient indices are natural numbers. The expression (z : Q) is the integer-to-rational coercion, "
                + "and the congruence and divisibility in the conclusion are over the integers.")),
            Node("IsGF", "The generating equation", Disp(Seq(Bound("A", Series()),
                Equal(Call("IsGF", F.Id("A")), EquationBody(F.Id("A"))))),
                "Formula (2): \"A(x) = 1 + 2*Sum_{n>=1} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n.\" "
                + "The unpaginated OEIS Formula section is expressed coefficientwise over Q.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The square residue conjecture", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "Comments: \"Conjecture: for n > 0, a(n) == 2 (mod 4) iff n is a square, and a(n) is divisible by 4 when n is nonsquare.\" "
                + "The unpaginated OEIS comment concerns the coefficients of the series in formula (2). "
                + "Here existence is included, and the residue assertion is stated for every rational solution. "
                + "The integer z equals its coefficient at each positive natural index n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Hanna's A380060 conjecture", Disp(ClaimBody()),
                "The integral coefficient iteration improves agreement by one degree. Its stabilized coefficients give an integer fixed point, "
                + "and the same contraction identifies every rational solution with its image in Q. "
                + "Modulo two the solution is one, so each unit quotient is one and its summand reduces to X^(m^2). "
                + "Thus half of each positive coefficient has the parity of the positive-square theta series. "
                + "Doubling gives residue two modulo four exactly at squares and divisibility by four at the other positive indices.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hanna-a380060-bilateral-theta-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a380060-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

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
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));

    private static Formula EquationBody(Formula a)
    {
        Formula m = F.Id("m"), n = F.Id("n"), x = F.Id("X");
        var term = Mul(Mul(Power(x, Power(n, D(2))), Power(Subtract(a, Power(x, n)), n)),
            Power(Power(Subtract(D(1), Mul(Power(x, n), a)), n), Seq(Minus, D(1))));
        var sum = Seq(new Formula.Subscript(Sum, Seq(n, Sp, InMacro, Sp, new Formula.Apply(Seq(Named("Finset"), Dot, Named("Icc")), [D(1), m]))), Sp, Parenthesized(term));
        return Equal(a, Call("mk", Seq(F.Id("m"), Colon, Sp, Naturals(), Sp, Mapsto, Sp,
            Call("coeff", m, Add(D(1), Mul(D(2), sum))))));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("A"), n = F.Id("n"), z = F.Id("z");
        var square = Call("IsSquare", n);
        var congruence = Seq(z, Sp, Equiv, Sp, D(2), Sp, Pmod, Grp(D(4)));
        var coefficient = Equal(Call("coeff", n, a), Parenthesized(Seq(z, Colon, Sp, Rationals())));
        var residues = And(Seq(Parenthesized(congruence), Sp, Iff, Sp, square),
            ImpliesFormula(Seq(Neg, Sp, square), Seq(Parenthesized(Seq(D(4), Colon, Sp, Integers())), Sp, Mid, Sp, z)));
        return And(Some("A", Series(), Call("IsGF", a)),
            Seq(Bound("A", Series()), ImpliesFormula(Call("IsGF", a),
                Seq(Bound("n", Naturals()), ImpliesFormula(Seq(D(0), Sp, Lt, Sp, n),
                    Some("z", Integers(), And(coefficient, residues)))))));
    }
}
