using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices;

internal sealed class FroeseGeorgePathCoverRankRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/froesegeorge2026pathcovers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A 15-element rooted poset has path-cover rank counts 15, 14, and 17 at ranks 6, 7, and 8.",
        H("A rank valley in a rooted path-cover lattice"),
        Blocks(
            Node("claim", "Froese–George Question 1", "claim", ClaimFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "In Definition 2, let P be any finite partial order with a least element. At each endpoint p, "
                    + "partition all saturated paths from the least element to p. Include the length-zero path "
                    + "at the least element. Along each Hasse edge, extension must take every block at the "
                    + "lower endpoint into a single block at the upper endpoint. A coarser family lies below a "
                    + "finer family. Sum the block count minus one over all endpoints to get its rank. "
                    + "The height H is the same sum for the singleton partitions. Question 1 asks whether "
                    + "the counts r(k) of families of rank k are log-concave at every interior rank "
                    + "or weakly unimodal with a mode between 0 and H."),
            Node("rank-counts", "Three consecutive rank counts", "witness_rank_counts", RankCounts(),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "Froese and George give the product of branch downset lattices in Remark 4, using "
                    + "Propositions 6–7. For this witness, two incomparable vertices cover the root. "
                    + "Both vertices are covered by the first vertex "
                    + "of each of two disjoint branches. Each branch has a three-vertex stem and three "
                    + "leaves covering its last stem vertex. Each of the twelve branch vertices has two "
                    + "saturated paths from the root, distinguished by the first step. The other three "
                    + "vertices each have one path. Extension within a branch preserves the first step. "
                    + "A split successor forces its predecessor to be split, so the split vertices in "
                    + "each branch form a lower ideal. Conversely, each pair of lower ideals uniquely "
                    + "determines the compatible family, with refinement corresponding to inclusion. "
                    + "The rank is the combined size of the two ideals and the height is 12. "
                    + "Lean checks the path classification and rank-preserving equivalence for this base, "
                    + "then enumerates the ideal pairs to give rank counts 15, 14, and 17 at ranks 6, 7, and 8."),
            Node("result", "Both shape properties fail on the same poset", "result", new Formula.Not(F.Id("claim")),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "The decrease from 15 to 14 requires any unimodal mode to precede rank 7. "
                    + "The increase from 14 to 17 requires it to follow rank 7. At rank 7, "
                    + "the square of 14 is 196 and the product of 15 and 17 is 255, contradicting "
                    + "log-concavity. This answers Question 1 for Definition 2's rooted lattice. "
                    + "The correspondence with count maps uses root preservation. "
                    + "Bare Definition 1 allows a singleton to map to the top of a two-element chain, "
                    + "where the path-count identity tests only the top-to-top path and the absence of a path to the bottom.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("froese-george-2026-path-cover-rank-question-1"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, DescribeRole role, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ClaimFormula()
    {
        var p = F.Id("P");
        var counts = Call("rankCount", p);
        var height = Call("sourceHeight", p);
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("P"), F.Id("Type"),
            Seq(OpenBracket, Call("PartialOrder", p), CloseBracket, Sp,
                OpenBracket, Call("OrderBot", p), CloseBracket, Sp,
                OpenBracket, Call("Fintype", p), CloseBracket, Comma, Sp,
                new Formula.Logic(Call("LogConcave", counts, height), FormulaLogicOperator.Or,
                    Call("Unimodal", counts, height))));
    }

    private static Formula RankCounts() => new Formula.Logic(RankCount(6, D(1, 5)), FormulaLogicOperator.And,
        new Formula.Logic(RankCount(7, D(1, 4)), FormulaLogicOperator.And, RankCount(8, D(1, 7))));

    private static Formula RankCount(byte rank, Formula count) =>
        new Formula.Relation(Call("rankCount", F.Id("Vertex"), D(rank)), FormulaRelationOperator.Equal, count);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
