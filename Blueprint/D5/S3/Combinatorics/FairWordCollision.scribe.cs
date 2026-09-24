using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class FairWordCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FairWordCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even overlapping fair binary blocks have collision probability two to minus their length.",
        H("Exact Collision Probability for Shifted Binary Words"),
        Blocks(
            Node("collision-words", "Collision contexts", "collisionWords", WordsFormula(),
                "One context x has length m+d. Its first block consists of positions zero "
                + "through m-1, and its second block starts at d. Equality means x(i) equals "
                + "x(i+d) for every i less than m. For d less than m these blocks overlap; "
                + "they are both read from the same context.", DescribeRole.Definition),
            Node("collision-probability", "The exact fair probability", "collisionProbability",
                ProbabilityFormula(), "Each binary context has mass one over two to the "
                + "power m+d. Counting those satisfying the equality constraints gives the "
                + "actual probability under independent fair bits.", DescribeRole.Definition),
            Node("fair-word-collision", "Exactly d free coordinates", "fair_word_collision",
                ResultFormula(), "The equality constraints are precisely a period-d condition "
                + "on the finite word. Every coordinate equals its coordinate modulo d. "
                + "Restriction to the first d positions is therefore injective on collision "
                + "contexts. Conversely every d-bit word extends by repetition to a "
                + "collision context, so restriction is a bijection. There are exactly two "
                + "to the power d such contexts, and dividing by the full cube size gives "
                + "two to the power minus m for every positive shift d.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula All(string n, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), domain, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Cube(Formula n) => new Formula.Power(Call("Fin", D(2)), Call("Fin", n));
    private static Formula Card(Formula a) => Seq(Lvert, a, Rvert);
    private static Formula Words(Formula m, Formula d) => Call("collisionWords", m, d);
    private static Formula WordsFormula()
    {
        var m = F.Id("m"); var d = F.Id("d"); var x = F.Id("x"); var i = F.Id("i");
        var property = All("i", Call("Fin", m),
            Eqn(new Formula.Apply(x, [i]), new Formula.Apply(x, [Add(i, d)])));
        return Disp(All("m", Nat(), All("d", Nat(), Eqn(Words(m, d),
            Seq(OpenBrace, x, InMacro, Cube(Add(m, d)), Mid, property, CloseBrace)))));
    }
    private static Formula ProbabilityFormula()
    {
        var m = F.Id("m"); var d = F.Id("d");
        return Disp(All("m", Nat(), All("d", Nat(), Eqn(Call("collisionProbability", m, d),
            new Formula.Fraction(Card(Words(m, d)), new Formula.Power(D(2), Add(m, d)))))));
    }
    private static Formula ResultFormula()
    {
        var m = F.Id("m"); var d = F.Id("d");
        return Disp(All("m", Nat(), All("d", Nat(), new Formula.Logic(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, d), FormulaLogicOperator.Implies,
            new Formula.Logic(Eqn(Card(Words(m, d)), new Formula.Power(D(2), d)), FormulaLogicOperator.And,
                Eqn(Call("collisionProbability", m, d), new Formula.Fraction(D(1), new Formula.Power(D(2), m))))))));
    }
}
