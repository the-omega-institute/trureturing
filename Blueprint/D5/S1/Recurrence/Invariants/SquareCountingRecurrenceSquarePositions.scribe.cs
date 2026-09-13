using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class SquareCountingRecurrenceSquarePositionsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/zumkeller2004a097602");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square positions and square values in Zumkeller's recurrence follow a nine-term pattern.",
        H("Square Positions and Values in a Square-Counting Recurrence"),
        Blocks(
            Node("a", "Zumkeller's square-counting recurrence", SequenceFormula(),
                "The source recurrence begins at index one. The Lean body assigns a(0)=0 only "
                + "as a sentinel outside the source. Its strong-recursive filter carries the "
                + "guard k<j+2; every k in Icc(1,j+1) satisfies this guard.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jovovic_a097602_positions", "Jovovic's square-position assertion",
                PositionFormula(),
                "For every positive index, the corresponding term is a square exactly when "
                + "the index is congruent to one or four modulo nine. The nine-term block "
                + "pattern separates every other term strictly between consecutive squares.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("zumkeller_a097602", "Zumkeller's square-value conjecture", ValueFormula(),
                "For every positive root m, its square occurs as a sequence value exactly when "
                + "m is not divisible by three. The two square positions in each block carry "
                + "the roots 3k+1 and 3k+2.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a097602-square-counting-recurrence-square-values"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a097602-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula SequenceFormula()
    {
        var j = F.Id("j");
        var k = F.Id("k");
        var successor = Add(j, D(1));
        var next = Add(j, D(2));
        var initial = Equal(Call("a", D(1)), D(1));
        var interval = Call("Icc", D(1), successor);
        var predicate = Parenthesized(Seq(
            k, Sp, Mapsto, Sp, Call("IsSquare", Call("a", k))));
        var squareCount = Call("card", Call("filter", interval, predicate));
        var recurrence = new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("j"), Naturals(),
            Equal(Call("a", next), Add(Call("a", successor), squareCount)));
        return Disp(new Formula.Logic(
            Parenthesized(initial), FormulaLogicOperator.And, Parenthesized(recurrence)));
    }

    private static Formula PositionFormula()
    {
        var n = F.Id("n");
        var positive = LessThanOrEqual(D(1), n);
        var residues = new Formula.Logic(
            Equal(new Formula.Modulo(n, D(9)), D(1)), FormulaLogicOperator.Or,
            Equal(new Formula.Modulo(n, D(9)), D(4)));
        var characterization = new Formula.Logic(
            Call("IsSquare", Call("a", n)), FormulaLogicOperator.Iff,
            Parenthesized(residues));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), Naturals(),
            new Formula.Logic(
                positive, FormulaLogicOperator.Implies, Parenthesized(characterization))));
    }

    private static Formula ValueFormula()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var occurrence = new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create("n"), Naturals(),
            new Formula.Logic(
                LessThanOrEqual(D(1), n), FormulaLogicOperator.And,
                Equal(Call("a", n), new Formula.Power(m, D(2)))));
        var characterization = new Formula.Logic(
            Parenthesized(occurrence), FormulaLogicOperator.Iff,
            NotEqual(new Formula.Modulo(m, D(3)), D(0)));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("m"), Naturals(),
            new Formula.Logic(
                LessThanOrEqual(D(1), m), FormulaLogicOperator.Implies,
                Parenthesized(characterization))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
