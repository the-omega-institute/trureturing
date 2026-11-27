using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class TestRingsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Test Rings", H("Test Rings"),
        Blocks(
            Paragraph(Text("Test rings: products, quotients, localisations; local rings are valuation rings of algebraically closed fields.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/TestRings.exists_valuationSubring_atPrime"),
                H("exists_valuationSubring_atPrime"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a test ring A and a prime p, the local ring A_p is an absolutely integrally closed local domain, and some valuation ring of an algebraically closed field is a localisation of A at p.")))))));
}
