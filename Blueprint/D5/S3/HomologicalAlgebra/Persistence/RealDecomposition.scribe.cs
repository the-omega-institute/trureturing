using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class RealDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/bauer2015persistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct and uniquely classify the actual natural real interval-sum decomposition.",
        H("Actual Natural Real Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-unique-decomposition"),
                DeclarationHandle.Create(Prefix + "exists_unique_decomposition"),
                H("Existence and uniqueness against arbitrary finite competitors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every arbitrary field, finite-dimensional finite diagram and strictly "
                            + "increasing real grid, choose the already constructed homogeneous "
                            + "interval basis. Birth is its birth breakpoint; death is the next "
                            + "breakpoint after its last vertex or infinity for a final survivor.")),
                    Paragraph(Text(
                        "Supported coordinate restriction, Basis.equivFun and its reconstruction "
                            + "sum give component isomorphisms. The existing occurrence naturality "
                            + "equations give all real arrow squares, including the zero prefix "
                            + "and unrestricted final tail. An empty or zero chain has an empty "
                            + "occurrence set. These coordinate suppliers are applied inside "
                            + "the substantive classification proof, not retained as a separate wrapper.")),
                    Paragraph(Text(
                        "Every competing finite positive-length interval family, with arbitrary "
                            + "real births and finite or infinite deaths, that is naturally isomorphic "
                            + "to the same actual module has the same endpoint occurrence counts. "
                            + "Component isomorphisms and naturality transport actual image ranks "
                            + "using the pinned range and finrank suppliers. The proof constructs "
                            + "the surviving-coordinate image equivalence, then uses common finite "
                            + "endpoint cuts and integer differences to isolate each multiplicity. "
                            + "Induced matching, quantitative estimates, exact interleaving iff "
                            + "matching and extended isometry remain separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-image-decomposition"),
                DeclarationHandle.Create(Prefix + "exists_image_decomposition"),
                H("Classifying the image of the same actual morphism"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The sorted union of both families' births and finite deaths determines "
                        + "a common grid. Endpoint membership establishes invertible source, "
                        + "target and image transports inside each cell. The zero prefix follows "
                        + "from actual target support, including an empty grid. Compatible "
                        + "sampled-image maps form a natural isomorphism to the same categorical "
                        + "image; finite-diagram classification constructs one image family. "
                        + "Both transported factors use that family and compose to the original "
                        + "morphism. A finite reindexing preserves arbitrary occurrence universes. "
                        + "Sorted birth and death fibers produce two embeddings of this same "
                        + "image family into source and target occurrences: the first preserves "
                        + "birth and bounds death, the second preserves death and bounds birth. "
                        + "Quantitative trim sandwiches and the exact interleaving "
                        + "converse are not conclusions of this theorem."))),
                DescribeRole.Theorem))));
}
