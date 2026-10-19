using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaA338632Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaA338632.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2026a338632");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's continued-fraction coefficients are two modulo four above degree one.",
        H("The OEIS A338632 Modulo-Four Congruence"),
        Blocks(
            Paragraph(Text("P. D. Hanna, OEIS A338632 revision 13 (no page), states verbatim: "
                + "\"G.f. A(x) satisfies: 1 = A(x) - x/(A(x) - 3*x/(A(x) - 5*x/(A(x) - 7*x/(A(x) - 9*x/(A(x) - ...))))), a continued fraction relation.\" "
                + "Its formula line states verbatim: \"a(n) = 2 (mod 4) for n > 1 (conjecture).\" "
                + "The formalization reads the relation through finite truncations, where tail(A,j,r) "
                + "is a rational power series and coeff(n,A) is the degree-n coefficient. "
                + "The operation smul is scalar multiplication, and val denotes the indicated rational cast.")),
            Node("tail", "Finite tails of the continued fraction", TailFormula(),
                "For rational PowerSeries A, tail(A,j,0)=A and the successor tail subtracts "
                + "the odd numerator (2j+1) times X divided by the next tail. The inverse is "
                + "the formal power-series inverse supplied by the coefficient field.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsGF", "The coefficientwise continued-fraction relation", IsGfFormula(),
                "IsGF(A) says that for every degree n, some truncation depth R makes the "
                + "degree-n coefficient of every later tail(A,0,r) equal to the constant series one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's modulo-four conjecture", ClaimFormula(),
                "The claim asserts existence of a series satisfying IsGF and says that every "
                + "such series has an integer coefficient congruent to two modulo four at each "
                + "degree n at least two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The modulo-four conjecture is proved", ClaimFormula(),
                "The normalized fixed-point construction supplies a series satisfying IsGF. "
                + "Reduction modulo four makes the odd numerators periodic with period two, "
                + "giving a quadratic equation. Its normalized root is (1+X^2)/(1-X), whose "
                + "coefficients from degree two onward are two modulo four.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("a338632-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Forall(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Coeff(Formula n, Formula series) => Call("coeff", n, series);
    private static Formula Tail(Formula a, Formula j, Formula r) => Call("tail", a, j, r);
    private static Formula Inv(Formula value) => Call("inv", value);
    private static Formula One() => D(1);

    private static Formula TailFormula()
    {
        var a = F.Id("A");
        var j = F.Id("j");
        var r = F.Id("r");
        var rationalJ = Parenthesized(Seq(Call("val", j), Colon, Sp, Rationals()));
        var numerator = Call("smul", Add(Multiply(D(2), rationalJ), D(1)), F.Id("X"));
        var successor = Equal(Tail(a, j, Add(r, D(1))),
            Subtract(a, Multiply(numerator, Inv(Tail(a, Add(j, D(1)), r)))));
        return Disp(Forall("A", Series(Rationals()), Forall("j", Naturals(),
            And(Equal(Tail(a, j, D(0)), a), Forall("r", Naturals(), successor)))));
    }

    private static Formula IsGfFormula()
    {
        var a = F.Id("A");
        var n = F.Id("n");
        var r = F.Id("r");
        var threshold = LessEqual(F.Id("R"), r);
        var equality = Equal(Coeff(n, Tail(a, D(0), r)), Coeff(n, One()));
        var rhs = Forall("n", Naturals(),
            Exists("R", Naturals(), Forall("r", Naturals(), Implication(threshold, equality))));
        return Disp(Forall("A", Series(Rationals()), new Formula.Logic(
            Call("IsGF", a), FormulaLogicOperator.Iff, Parenthesized(rhs))));
    }

    private static Formula ClaimFormula()
    {
        var a = F.Id("A");
        var n = F.Id("n");
        var m = F.Id("m");
        var existence = Exists("A", Series(Rationals()), Call("IsGF", a));
        var congruence = Exists("m", Integers(), And(
            Equal(Coeff(n, a), Parenthesized(Seq(Call("val", m), Colon, Sp, Rationals()))),
            Equal(new Formula.Modulo(m, D(4)), D(2))));
        var universal = Forall("A", Series(Rationals()), Implication(Call("IsGF", a),
            Forall("n", Naturals(), Implication(LessEqual(D(2), n), congruence))));
        return Disp(And(existence, universal));
    }
}
