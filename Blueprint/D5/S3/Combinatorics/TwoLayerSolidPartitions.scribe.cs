using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class TwoLayerSolidPartitionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoLayerSolidPartitions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/meeussen2025a381265");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-layer solid partitions whose first layer is a plane partition of n and whose second layer is a plane partition of 3 number 3(2 A000219(n) - A000990(n) - 2 A000041(n) + 1), with A000219 the plane partitions, A000990 the plane partitions with at most two rows and A000041 the partitions of n, as conjectured by W. Meeussen for OEIS A381265.",
        H("Two-layer solid partitions with a second layer of size 3"),
        Blocks(
            Node("plane", "Plane partitions", PlaneFormula(),
                "A000219(n), the plane partitions of n read through their diagrams: the lower sets of n cells of the cube of the natural numbers (IsSolidPartition of SolidPartitionFirstColumn in dimension 3).",
                "planeCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tworow", "Plane partitions with at most two rows", TwoRowFormula(),
                "A000990(n), the plane partitions of n whose cells all have first coordinate (row index) at most 1.",
                "twoRowCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The sequence A381265", AFormula(),
                "The pairs of a plane partition P1 of n (the first layer) and a plane partition P2 of 3 (the second layer) with P2 contained in P1, which are the two-layer solid partitions counted by the entry, whose data start a(3) = 6.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Meeussen's conjecture", ClaimFormula(),
                "For every n the count equals three times 2 A000219(n) - A000990(n) - 2 A000041(n) + 1, with A000041(n) the number of partitions of n; both sides vanish for n < 3.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "The plane partitions of 3 are six: the three lines {0, e_k, 2 e_k} and the three corners {0, e_i, e_j}. A plane partition of n contains the line in direction k exactly when some cell has k-th coordinate at least 2, so by the bijections that permute the coordinates the three lines are each contained in A000219(n) - A000990(n) plane partitions of n. It contains the corner {0, e_i, e_j} exactly when it contains e_i and e_j. The plane partitions of n without e_i lie in the coordinate plane x_i = 0 and are the lower sets of n cells of the square of the natural numbers, which are the Young diagrams of the partitions of n (row lengths); those without e_i and e_j lie on the remaining axis, one for each n. So each corner is contained in A000219(n) - 2 A000041(n) + 1 of them, and summing over the six second layers gives the formula.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("meeussen-2025-a381265-two-layer-solid"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("twolayer-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Count(Formula variable, Formula condition) =>
        new Formula.Absolute(Seq(OpenBrace, variable, Sp, Mid, Sp, condition, CloseBrace));
    private static Formula Solid(Formula size, Formula cells) => Call("IsSolidPartition", size, cells);
    private static Formula AsInt(Formula value) =>
        Seq(Open, value, Colon, Sp, new Formula.Integers(), Close);

    private static Formula PlaneFormula()
    {
        Formula n = F.Id("n"), cells = F.Id("I");
        return Disp(Equal(Call("planeCount", n), Count(cells, Solid(n, cells))));
    }

    private static Formula TwoRowFormula()
    {
        Formula n = F.Id("n"), cells = F.Id("I"), c = F.Id("c");
        Formula rows = All("c", cells, AtMost(new Formula.Subscript(c, D(0)), D(1)));
        return Disp(Equal(Call("twoRowCount", n), Count(cells, And(Solid(n, cells), rows))));
    }

    private static Formula AFormula()
    {
        Formula n = F.Id("n"), first = F.Id("P1"), second = F.Id("P2");
        Formula pair = Seq(Open, first, Comma, Sp, second, Close);
        return Disp(Equal(Call("a", n), Count(pair,
            And(Solid(n, first), And(Solid(D(3), second), SubsetOf(second, first))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula partitions = AsInt(new Formula.Absolute(Call("Partition", n)));
        Formula inner = Add(Subtract(Subtract(Times(D(2), AsInt(Call("planeCount", n))),
            AsInt(Call("twoRowCount", n))), Times(D(2), partitions)), D(1));
        return Disp(Iff(F.Id("claim"), All("n", Naturals(),
            Equal(AsInt(Call("a", n)), Times(D(3), Parenthesized(inner))))));
    }
}
