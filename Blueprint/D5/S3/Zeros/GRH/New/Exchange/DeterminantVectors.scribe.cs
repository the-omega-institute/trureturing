using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class DeterminantVectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Determinant Vectors", H("Determinant Vectors"),
        Blocks(
            Paragraph(Text("Determinant vectors in Fock space are cone integrals of determinant vectors one floor up.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/DeterminantVectors.surjOn_cone_integral_detVectors"),
                H("surjOn_cone_integral_detVectors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let W′, V′ be W, V plus a hyperbolic plane, with adapted splittings, z ≥ 1 and rk W′ = 2k + 2·(negative signs of W′). Every determinant vector v (detVectors k m) is the cone integral at z, with weights k + m, of a determinant vector v′.")))))));
}
