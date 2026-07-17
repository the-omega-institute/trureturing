using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class MinkowskiModelSetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Scale/MinkowskiModelSet",
            "The two real embeddings form a golden lattice whose internal window selects model-set points."),
        H("Golden Minkowski Model Set"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("minkowski-lattice-window-and-labeled-model-set"),
                DescribeKind.Definition,
                H("Minkowski lattice, window, and labeled model set"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec")),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/baakefrankgrimm2021three")),
                Blocks(Paragraph(Text(
                    "The physical and conjugate embeddings give an injective diagonal range. An internal-space window selects physical projections, and the labeled extension pairs selected points with their joint golden coordinates.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("value-and-code-geometries"),
                DescribeKind.Remark,
                H("Value and code geometries"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec")),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/baakefrankgrimm2021three")),
                Blocks(Paragraph(Text(
                    "The same carrier admits a lattice-like value reading and a cut-and-project code reading. The internal window justifies calling the code geometry a model set; it does not by itself provide a Bloch decomposition, a spectral gap theorem, or a periodic classifier for the code layer.")))))));
}
