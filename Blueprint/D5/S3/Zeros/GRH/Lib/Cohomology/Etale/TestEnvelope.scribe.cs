using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class TestEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Test Envelope", H("Test Envelope"),
        Blocks(
            Paragraph(Text("Functorial envelope: maps from given rings to tests factor through a test ring.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/TestEnvelope.exists_functorial_test"),
                H("exists_functorial_test"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For any family of commutative rings R_o, there are an endofunctor E of commutative rings with every E(A) a test ring and a natural map θ: A → E(A) such that every homomorphism from an R_o to a test ring factors through θ at R_o.")))))));
}
