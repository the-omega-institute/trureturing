using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeEnumerationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indexed compositions support the cyclic partition count.",
        H("Crown composition enumeration"),
        Blocks(
            Paragraph(Text("The parity-adjusted composition construction follows source Lemma 3.5, with an equivalence stated for all natural parameters, including empty and impossible cases. Original-block connectivity supplies a formal detail of the cycle argument in Lemma 3.2.")),
            Describe.Lean(
                DescribeId.Create("parity-composition-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration.parityCompositionEquiv"),
                H("Prescribed odd parts and evenization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The explicit equivalence separates an indexed composition with a prescribed number of odd parts into the set of odd positions and the positive residual composition obtained by parity adjustment. This implements the composition step of the published enumeration; support and inverse maps are part of the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crown-partition-original-block-cycle-graph-connected"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration.crownPartition_originalBlock_cycleGraph_connected"),
                H("Original blocks are connected in the cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For n at least two, an original-vertex block of an augmented connected compatible partition that meets neither endpoint induces a connected subgraph of the cycle on 2n vertices. The alternating order relation is related to the undirected cycle before the block path is extracted."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP"))
        ]));
}
