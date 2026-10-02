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
                DescribeId.Create("decomposition"), DeclarationHandle.Create(Prefix + "Decomposition"),
                H("The full real decomposition object"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The output has one finite occurrence type, positive real half-open intervals "
                        + "with finite or infinite deaths, and an actual natural isomorphism from "
                        + "the real module to their supported coordinate sum. Universe lifting "
                        + "allows the field and original vector-space carriers to inhabit "
                        + "independent universes; it changes neither the maps nor the field."))),
                DescribeRole.Definition),
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
                DescribeRole.Theorem))));
}
