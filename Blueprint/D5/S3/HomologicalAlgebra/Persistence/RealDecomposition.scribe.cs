using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class RealDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/bauer2015persistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the actual natural finite interval-sum decomposition of a real finite-chain extension.",
        H("Actual Natural Real Decomposition"),
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
                DescribeId.Create("decompose"), DeclarationHandle.Create(Prefix + "decompose"),
                H("Apply the supplied constructive basis and coordinate suppliers"),
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
                            + "occurrence set. This necessary object constructor is supplier "
                            + "transport, not an additional content theorem or escape witness.")),
                    Paragraph(Text(
                        "Uniqueness is a distinct actual-image and common-endpoint-cut result. "
                            + "Induced matching, quantitative estimates, exact interleaving iff "
                            + "matching and extended isometry remain separate obligations."))),
                DescribeRole.Definition))));
}
