using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class MovesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/Moves.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/chen2026combinatorialrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite simple graph counts, tight subsets, and exact Henneberg operations over arbitrary vertex types.",
        H("Henneberg preservation and reconstruction"), Blocks(
            Describe.Lean(DescribeId.Create("moves-0"), DeclarationHandle.Create(Prefix + "IsLaman"),
                H("Laman counts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every simple graph, the Laman property is (2,3)-tightness: every eligible finite subset obeys its induced-edge bound and the total edge count meets it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("moves-1"), DeclarationHandle.Create(Prefix + "two_le_degree"),
                H("Minimum degree in the nonbase case"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A Laman graph on at least three vertices has degree at least two at every vertex. Apply sparsity to the complement of that vertex and use the partition of all edges into incident and nonincident edges."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moves-2"), DeclarationHandle.Create(Prefix + "eq_top_of_card_eq_two"),
                H("The two-vertex base"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A Laman graph on exactly two vertices is complete. Tightness gives one edge, and inclusion in the complete graph with the same finite edge count gives equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moves-3"), DeclarationHandle.Create(Prefix + "top_fin_two_isLaman"),
                H("K2 satisfies the counts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The complete graph on Fin 2 is Laman. It has one edge, and the only eligible subset is the whole two-vertex set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moves-4"), DeclarationHandle.Create(Prefix + "typeI"),
                H("Type I adjacency"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every G and old vertices a,b, the output lives on Option V. Two some-vertices are adjacent exactly when their old vertices were adjacent; none is adjacent to some u exactly when u=a or u=b; none has no loop. A legal move additionally requires a != b."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("moves-5"), DeclarationHandle.Create(Prefix + "typeII"),
                H("Type II adjacency"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every G and old vertices a,b,c, two some-vertices remain adjacent exactly when they were adjacent and their unordered pair differs from {a,b}. The fresh none vertex is adjacent exactly to some a, some b and some c, and has no loop. A legal move requires the actual old edge ab and all three old vertices distinct."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("moves-6"), DeclarationHandle.Create(Prefix + "typeI_isLaman"),
                H("Type I preserves Laman counts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite Laman G and distinct old vertices a,b, its Type I extension is Laman. For each induced subset, separate old edges from its at most two fresh edges; subsets omitting the fresh vertex inherit the old bound directly. The total count increases by two edges and one vertex."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moves-7"), DeclarationHandle.Create(Prefix + "typeII_isLaman"),
                H("Type II preserves every induced-subset bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite Laman G, actual edge ab and third vertex c distinct from both endpoints, its Type II extension is Laman. For an induced subset, remove none to obtain its old part, subtract the bridge when present, and count the fresh incident edges. If all three neighbors occur, the deleted old edge supplies the required unit of slack. Otherwise there are at most two fresh edges; the one-vertex and empty old parts are handled separately. The proof covers every subset and does not assume planarity or placement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moves-8"), DeclarationHandle.Create(Prefix + "isoTypeIOfTwoNeighbors"),
                H("Exact Type I reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("If the neighbors of v are exactly a and b, with both different from v, Option of the vertex-deletion subtype is isomorphic to the original graph. The equivalence sends the unique fresh none vertex to v and some w to its original old vertex; all four adjacency cases are checked."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("moves-9"), DeclarationHandle.Create(Prefix + "isoTypeIIOfThreeNeighbors"),
                H("Exact Type II reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("If the neighbors of v are exactly a,b,c, none equals v, and a,b are not adjacent in the original graph, repair the deletion graph by adding ab. Applying Type II deletes exactly that bridge. The Option/subtype equivalence preserves every other old adjacency and gives precisely the original incident edges at v."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("moves-10"), DeclarationHandle.Create(Prefix + "exists_typeI_or_typeII_reverse"),
                H("A smaller Laman graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every finite Laman graph on at least three vertices admits a Type I or Type II reverse to a Laman graph on the subtype excluding one vertex. Minimum degree excludes the pendant case. Type I tightness follows by reconstruction and reverse preservation; Type II tightness follows from the safe sparse repair, the actual bridge edge, and the exact edge count."))), DescribeRole.Theorem)), []));
}
