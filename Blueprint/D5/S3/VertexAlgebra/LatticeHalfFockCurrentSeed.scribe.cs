using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCurrentSeedDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplication through the charged correction",
        H("Multiplication through the charged correction"),
        Blocks(
            Paragraph(Text("The correction field is the original charged correctedPolynomial. Multiplication by a source variable adds its physical normal insertion, the charged singleton term and the pair contractions over every source index.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentseed-multiplication"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeed.correctedPolynomial_X_mul"),
                H("Corrected polynomial multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The pair sum is supported on the variables of the input polynomial. Partial differentiation removes labelled occurrences with their actual multiplicities. The proof evaluates the original correctionLift insertion and transports every correction shift through normalInsertion. The resulting identity supplies the physical current seed."))),
                DescribeRole.Theorem),
            Paragraph(Text("The original singletonPolynomial and pairPolynomial coefficients remain unchanged. The field evaluation is coefficient extraction followed by the existing normalPolynomial and even correction shifts; it is not a replacement state-field map.")))));
}
