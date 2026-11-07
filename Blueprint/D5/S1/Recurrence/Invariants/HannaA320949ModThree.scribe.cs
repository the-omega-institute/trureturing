using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaA320949ModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaA320949ModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/hanna2018a320949");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The OEIS A320949 coefficientwise generating equation has a rational solution whose positive coefficients are all divisible by three.",
        H("Hanna's OEIS A320949 Modulo-Three Conjecture"),
        Blocks(
            Paragraph(Text("Paul D. Hanna, OEIS A320949 revision 12 (2018-11-25), states verbatim: "
                + "\"G.f. A(x) satisfies: Sum_{n>=0} (1+x)^(n^2) / (1 + A(x))^(n+1)  =  1.\" "
                + "Its formula line states verbatim: \"a(n) = 0 (mod 3) for n > 0 (conjecture).\" "
                + "The coefficient a(n) is [x^n]A(x), and the displayed example fixes A(0)=1. "
                + "The infinite sum is read coefficientwise through convergent rational sums in the usual topology.")),
            Node("term", "The nth summand", TermFormula(),
                "The source summand is (1+x)^(n^2)/(1+A(x))^(n+1). The denominator has constant coefficient two, so its inverse is the formal power-series inverse after the literal normalization IsGF(A).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsGF", "The coefficientwise generating equation", IsGFFormula(),
                "IsGF(A) fixes the constant coefficient and requires, for every natural degree k, that the rational coefficient sum of the nth summands equals the coefficient of the constant series one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's modulo-three conjecture", ClaimFormula(),
                "The proposition asserts existence of a rational solution and says that every rational solution has each positive-degree coefficient equal to an integer multiple of three. The integer witness expresses integrality rather than assuming it.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The modulo-three conjecture is proved", ClaimBodyFormula(),
                "Finite Newton expansion of the even polynomial t ↦ choose(t^2,k) gives an integral transform. Reciprocity forces the positive rows of that transform to vanish modulo three, and coefficientwise contraction gives a unique normalized fixed point over every commutative coefficient ring. Mapping the integral fixed point to the rationals establishes the coefficientwise equation, while reduction to ZMod(3) forces every positive coefficient to vanish there.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a320949-hanna-mod-three"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("hanna-a320949-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Bound(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Implies(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, F.Implies, Sp, Parenthesized(conclusion));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Coeff(Formula n, Formula series) => Call("coeff", n, series);
    private static Formula Positive(Formula n) => Seq(D(0), Sp, Lt, Sp, n);

    private static Formula TermBody(Formula a, Formula j) =>
        Mul(Pow(Add(D(1), F.Id("X")), Pow(j, D(2))),
            Call("inv", Pow(Add(D(1), a), Add(j, D(1)))));

    private static Formula TermFormula() =>
        Disp(Bound("A", Series(), Bound("j", Naturals(),
            Equal(Call("term", F.Id("A"), F.Id("j")),
                TermBody(F.Id("A"), F.Id("j"))))));

    private static Formula IsGFBody()
    {
        var a = F.Id("A");
        var k = F.Id("k");
        var j = F.Id("j");
        return And(Equal(Call("constantCoeff", a), D(1)),
            Bound("k", Naturals(),
                Call("HasSum", Lambda("j", Naturals(), Coeff(k, Call("term", a, j))),
                    Coeff(k, D(1)))));
    }

    private static Formula IsGFFormula() =>
        Disp(Bound("A", Series(), Equal(Call("IsGF", F.Id("A")), Parenthesized(IsGFBody()))));

    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var n = F.Id("n");
        var z = F.Id("z");
        var divisibility = Exists("z", Integers(),
            Equal(Coeff(n, a), Cast(Mul(D(3), z), Rationals())));
        return And(Exists("A", Series(), Call("IsGF", a)),
            Bound("A", Series(), Implies(Call("IsGF", a),
                Bound("n", Naturals(), Implies(Positive(n), divisibility)))));
    }

    private static Formula ClaimFormula() =>
        Disp(Equal(Named("claim"), Parenthesized(ClaimBody())));

    private static Formula ClaimBodyFormula() => Disp(ClaimBody());
}
