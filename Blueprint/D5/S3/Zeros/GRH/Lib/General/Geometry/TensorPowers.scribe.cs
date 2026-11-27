using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class TensorPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor Powers", H("Tensor Powers"),
        Blocks(
            Paragraph(Text("Projective embeddings by linear systems: properness, closed immersions, Segre, affine charts. Tensor products and powers of line bundles; Segre and Veronese embeddings.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/TensorPowers.isProjEmbedding_pi"),
                H("isProjEmbedding_pi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Segre: let W be proper over S, with finitely many S-maps π_l: W → Z_l that jointly separate morphisms into W over S. If each N_l satisfies LineBundle.IsProjEmbedding on Z_l, so does the Segre product of the π_l^*N_l on W.")))))));
}
