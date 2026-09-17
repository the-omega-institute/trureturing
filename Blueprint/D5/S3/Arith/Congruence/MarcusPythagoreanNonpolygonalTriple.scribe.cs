using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class MarcusPythagoreanNonpolygonalTripleDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/marcus2021a344083");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-four-five triple is the unique positive Pythagorean triple whose sides all belong to A090467.",
        H("Marcus's A344083 Pythagorean Triple Conjecture"),
        Blocks(
            Node("polygonal", "Polygonal numbers", PolygonalFormula(),
                "All operations are in the natural numbers. The operator choose denotes "
                    + "Nat.choose, and subtraction is truncated. For k and m above two, "
                    + "this subtraction-free value equals 1+k*m*(m-1) div 2-(m-1)^2, "
                    + "where div is natural floor division; this is the formula printed "
                    + "in the definition of A090467.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("nonpolygonal", "The A090467 predicate", NonpolygonalFormula(),
                "A natural number is nonpolygonal when it has no representation by the "
                    + "displayed polygonal formula with both the order and the index "
                    + "strictly greater than two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Marcus's uniqueness conjecture", ClaimFormula(),
                "The sides three, four, and five are nonpolygonal and satisfy the "
                    + "Pythagorean equation. For any positive legs x and y satisfying that "
                    + "equation, if all three sides are nonpolygonal, then the unordered "
                    + "finset of legs is {3,4} and the hypotenuse is 5. The third "
                    + "nonpolygonal hypothesis is retained even though the uniqueness "
                    + "proof needs only the two leg hypotheses.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The unique nonpolygonal Pythagorean triple", ResultFormula(),
                "Reduction modulo three shows that one leg is divisible by three. A positive "
                    + "nonpolygonal multiple of three must equal three, because every larger "
                    + "multiple 3t has the polygonal representation polygonal(t+1,3). The "
                    + "Pythagorean equation then bounds and determines the other leg and the "
                    + "hypotenuse as four and five.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("a344083-" + name),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula PolygonalFormula()
    {
        var k = F.Id("k");
        var m = F.Id("m");
        var value = Add(m, Multiply(Subtract(k, D(2)), Call("choose", m, D(2))));
        return Disp(ForAll([Bound("k"), Bound("m")],
            Equal(Call("polygonal", k, m), value)));
    }

    private static Formula NonpolygonalFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var m = F.Id("m");
        var representation = And(
            Less(D(2), k),
            And(Less(D(2), m), Equal(n, Call("polygonal", k, m))));
        var absence = Not(Exists([Bound("k"), Bound("m")], representation));
        return Disp(ForAll([Bound("n")],
            Iff(Call("nonpolygonal", n), absence)));
    }

    private static Formula ClaimFormula()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var z = F.Id("z");
        var equation = Equal(
            Add(new Formula.Power(x, D(2)), new Formula.Power(y, D(2))),
            new Formula.Power(z, D(2)));
        var existence = And(
            Call("nonpolygonal", D(3)),
            And(Call("nonpolygonal", D(4)),
                And(Call("nonpolygonal", D(5)),
                    Equal(
                        Add(new Formula.Power(D(3), D(2)), new Formula.Power(D(4), D(2))),
                        new Formula.Power(D(5), D(2))))));
        var conclusion = And(
            Equal(Pair(x, y), Pair(D(3), D(4))),
            Equal(z, D(5)));
        var body = Implies(Less(D(0), x),
            Implies(Less(D(0), y),
                Implies(equation,
                    Implies(Call("nonpolygonal", x),
                        Implies(Call("nonpolygonal", y),
                            Implies(Call("nonpolygonal", z), conclusion))))));
        var uniqueness = ForAll([Bound("x"), Bound("y"), Bound("z")], body);
        return Disp(Iff(F.Id("claim"), And(existence, uniqueness)));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula.BoundVariable Bound(string name) => new(
        FormulaIdentifier.Create(name), Naturals());

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(OpenBrace, left, Comma, Sp, right, CloseBrace);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Not(Formula value) =>
        Seq(Neg, Parenthesized(value));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
