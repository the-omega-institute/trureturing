using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class SafeRepairDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/SafeRepair.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/chen2026combinatorialrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite simple graph counts, tight subsets, and exact Henneberg operations over arbitrary vertex types.",
        H("Safe nonedge repair by tight blockers"), Blocks(
            Describe.Lean(DescribeId.Create("saferepair-0"), DeclarationHandle.Create(Prefix + "no_isTightOn_excluding_three_neighbors"),
                H("The three-neighbor obstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("In a (2,3)-sparse graph, no tight set excluding v contains three distinct neighbors a,b,c of v. Inserting v adds one vertex and at least three distinct actual edges, contradicting sparsity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saferepair-1"), DeclarationHandle.Create(Prefix + "contradiction_one_pair"),
                H("One blocked pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A tight blocker for one neighbor pair, together with actual edges for the other two pairs, produces a tight set containing all three neighbors and excluding the removed vertex. The three-neighbor obstruction rules this out. Every adjacency and membership assumption in the Lean statement is used in that construction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saferepair-2"), DeclarationHandle.Create(Prefix + "contradiction_two_pair"),
                H("Two blocked pairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Two tight pair blockers and the actual remaining pair edge cannot coexist around three distinct neighbors. If their intersection is large, tight union applies. In the remaining singleton-intersection case, the third pair edge supplies the missing bonus edge."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saferepair-3"), DeclarationHandle.Create(Prefix + "contradiction_three_pair"),
                H("Three blocked pairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Three tight pair blockers cannot coexist around three distinct neighbors. Pairwise intersections and tight union or bonus-edge closure construct a forbidden tight set containing all three neighbors. The small-intersection cases are handled within the same actual finite sets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saferepair-4"), DeclarationHandle.Create(Prefix + "False_of_pairwise_blocker_or_edge"),
                H("The pair dispatcher"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For each of the three neighbor pairs, assume either the actual pair edge exists or a tight blocker excludes the removed vertex and contains that pair. Exhausting the edge/blocker choices gives a contradiction using the one-, two-, or three-blocker construction and the all-edges obstruction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saferepair-5"), DeclarationHandle.Create(Prefix + "typeII_reverse_blocker"),
                H("Extracting a genuine tight blocker"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For distinct nonadjacent old neighbors x,y of v, form the induced graph after deleting v and add the bridge xy. If that graph fails (2,3)-sparsity, a violating finite subset transports back to a tight subset of the original graph containing x and y and excluding v. Deleting the one added bridge and squeezing with the original sparsity bound establishes exact tightness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saferepair-6"), DeclarationHandle.Create(Prefix + "exists_typeI_or_typeII_reverse"),
                H("A safe reverse move"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every finite (2,3)-sparse graph with an edge has a degree-one, degree-two, or degree-three reverse decomposition. In the degree-three case there are three distinct old neighbors and a genuinely nonadjacent pair whose bridge can safely be inserted after vertex deletion. If every nonedge pair were unsafe, blocker extraction and the pair dispatcher would contradict sparsity. This supplies a safe repair without a decomposition hypothesis."))), DescribeRole.Theorem)), []));
}
