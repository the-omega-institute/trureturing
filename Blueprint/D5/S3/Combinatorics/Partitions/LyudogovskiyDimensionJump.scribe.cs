using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class LyudogovskiyDimensionJumpDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/lyudogovskiy2026dimensionjump");

    public DocumentDefinition Create()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var p = F.Id("p");
        var q = F.Id("q");
        var nat = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var size = Sub(new Formula.Binary(D(3), FormulaBinaryOperator.Multiply, k), D(1));
        var pDimension = Apply("localDimension", p);
        var qDimension = Apply("localDimension", q);
        var difference = Sub(IntegerCast(pDimension), IntegerCast(qDimension));
        var absoluteDifference = Seq(Lvert, Sp, difference, Sp, Rvert);
        var bound = All("n", nat, Implies(Less(D(0), n),
            All("p", Apply("Partition", n), All("q", Apply("Partition", n),
                Implies(Apply("Adj", Apply("graph", n), p, q), LessEqual(absoluteDifference, D(2)))))));
        var firstRows = Seq(OpenBracket, k, Comma, k, Comma, Sub(k, D(2)), Comma, D(1), CloseBracket);
        var secondRows = Seq(OpenBracket, k, Comma, k, Comma, Sub(k, D(1)), CloseBracket);
        var witness = And(Equal(Apply("rowLens", Apply("ofPartition", p)), firstRows),
            And(Equal(Apply("rowLens", Apply("ofPartition", q)), secondRows),
                And(Apply("Adj", Apply("graph", size), p, q),
                    And(Equal(pDimension, D(4)), Equal(qDimension, D(2))))));
        var sharp = All("k", nat, Implies(LessEqual(D(4), k),
            Exists("p", Apply("Partition", size), Exists("q", Apply("Partition", size), witness))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The sharp absolute local simplex dimension jump across a partition transfer is two.",
            H("A sharp bound on the local simplex dimension jump"), Blocks(
                Describe.Lean(DescribeId.Create("lyudogovskiy-sharp-dimension-jump"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/LyudogovskiyDimensionJump.result"),
                    H("Universal bound and a sharp family"),
                    StatementSource.FromAuthor(Disp(And(bound, sharp))),
                    AssessedProvenance.FromRepo(Source), Blocks(
                        Paragraph(Text("Partition(n) consists of all integer partitions of n. Adj(graph(n), p, q) holds for one nontrivial unit transfer between distinct part occurrences, with a virtual zero recipient allowed. localDimension(p) is the maximum clique size through p minus one. rowLens(ofPartition(p)) lists the row lengths of the Young diagram of p in weakly decreasing order. Each dimension in the universal bound is cast to the integers before subtraction.")),
                        Paragraph(Text("A clique of size at least two lies above a common predecessor or below a common successor. The available corners are counted by distinct positive row lengths, with one additional corner for starting a row. Across a one-cell change, at most one positive length is gained and at most one is lost. Two adjacent diagrams share a predecessor and a successor, so counting the actual cliques built on those diagrams bounds the change in either direction.")),
                        Paragraph(Text("For the displayed family, the shared predecessor is (k, k, k−2). Its extensions give a clique of dimension two through the second endpoint. All deletions from that endpoint have at most two distinct positive lengths, and its successors have at most three, giving the matching upper bound. Deleting from the second row of the first endpoint leaves four distinct positive lengths. Its extensions give dimension at least four, and the universal bound gives the matching upper bound."))),
                    DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("lyudogovskiy-2026-dimension-jump"),
                        ResolutionKind.Proved)))));
    }

    private static Formula Apply(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula IntegerCast(Formula value) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, Mathbb, Grp(F.Id("Z"))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
