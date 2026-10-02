using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class NearestNeighborFreezingUniqueMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/enciso2007nearestneighbor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nearest-neighbor QES chain potential has a unique minimum at its site configuration.",
        H("Unique minimum of the nearest-neighbor QES chain potential"),
        Blocks(
            Node("sites", "The cyclic site equations", SitesFormula(),
                "Sites ξ expresses Eq. (6). The cyclic successor is finRotate(N), and its inverse is the predecessor. StrictMono ξ imposes the increasing chamber separately; Fin N uses zero-based indices.",
                "Sites", DescribeRole.Definition),
            Node("potential", "The nearest-neighbor potential", UFormula(),
                "The potential is Eq. (31), with r² = Σ_i x_i² and the two nearest-neighbor interaction sums.",
                "U", DescribeRole.Definition),
            Node("claim", "The unique-minimum claim", ClaimFormula(),
                "The paper states after Eqs. (31)–(32), printed p. 13: \"The first one is the requirement that ξ be the unique minimum of the potential U in the domain C. Although our numerical calculations suggest that this is indeed the case, we have not been able to provide a rigorous proof of this fact.\" The encoding uses StrictMono on Fin N → ℝ and cyclic predecessor and successor indices.",
                "claim", DescribeRole.Definition),
            Node("result", "The unique-minimum theorem", ClaimFormula(),
                "For every N ≥ 3, the site configuration supplied by the theorem is the unique minimizer of U on the strictly increasing chamber.",
                "result", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role) => Describe.Lean(
        DescribeId.Create("nearest-neighbor-" + id), DeclarationHandle.Create(Prefix + declaration),
        H(title), StatementSource.FromAuthor(formula),
        (role == DescribeRole.Theorem ? AssessedProvenance.FromRepo() : AssessedProvenance.FromLiterature(Source)),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Fn(Formula n) => new Formula.TypeArrow(Fin(n), Real());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula Sum(Formula n, Formula i, Formula body) =>
        Seq(new Formula.Subscript(FormulaDsl.Sum, Seq(i, InMacro, Fin(n))), Sp, body);
    private static Formula Next(Formula n, Formula i) => Apply(Call("finRotate", n), i);
    private static Formula Prev(Formula n, Formula i) => Apply(Call("symm", Call("finRotate", n)), i);
    private static Formula SitesFormula()
    {
        var n = F.Id("N");
        var xi = F.Id("xi");
        var i = F.Id("i");
        var rhs = Add(Div(D(1), Sub(Apply(xi, i), Apply(xi, Prev(n, i)))),
            Div(D(1), Sub(Apply(xi, i), Apply(xi, Next(n, i)))));
        return Disp(All("N", Nats(), All("xi", Fn(n),
            Equal(Call("Sites", xi), All("i", Fin(n), Equal(Apply(xi, i), rhs))))));
    }
    private static Formula UFormula()
    {
        var n = F.Id("N");
        var x = F.Id("x");
        var i = F.Id("i");
        var xi = Apply(x, i);
        var next = Apply(x, Next(n, i));
        var prev = Apply(x, Prev(n, i));
        var body = Add(Add(Sum(n, i, Sq(xi)),
            Sum(n, i, Div(D(2), Sq(Parenthesized(Sub(xi, next)))))),
            Sum(n, i, Div(D(2), Mul(Parenthesized(Sub(xi, prev)),
                Parenthesized(Sub(xi, next))))));
        return Disp(All("N", Nats(), All("x", Fn(n), Equal(Call("U", x), body))));
    }
    private static Formula ClaimFormula()
    {
        var n = F.Id("N");
        var xi = F.Id("xi");
        var x = F.Id("x");
        var equality = Parenthesized(Seq(
            Call("U", x), Sp, Eq, Sp, Call("U", xi), Sp,
            Rightarrow, Sp, x, Sp, Eq, Sp, xi));
        var minimum = Parenthesized(Seq(
            Call("U", x), Sp, Geq, Sp, Call("U", xi), Sp,
            Land, Sp, equality));
        var body = Ex("xi", Fn(n), Seq(
            Call("StrictMono", xi), Sp, Land, Sp,
            Call("Sites", xi), Sp, Land, Sp,
            Parenthesized(All("x", Fn(n), Seq(
                Call("StrictMono", x), Sp, Rightarrow, Sp, minimum)))));
        return Disp(All("N", Nats(), Parenthesized(Seq(
            D(3), Leq, Sp, n, Sp, Rightarrow, Sp, body))));
    }
}
