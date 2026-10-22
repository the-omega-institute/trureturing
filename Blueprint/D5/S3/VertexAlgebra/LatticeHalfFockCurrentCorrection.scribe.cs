using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCurrentCorrectionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full charged correction commutes with source partial derivatives",
        H("The full charged correction commutes with source partial derivatives"),
        Blocks(
            Paragraph(Text("The operator is exactly the original Corr. Its correctionWord has the original singletonPolynomial, pairPolynomial and pairDerivation; no neutral substitution or alternative correction map is used.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentcorrection-corr-partial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.Corr_partial"),
                H("The full charged correction commutes with source partial derivatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The source derivative at any ordinary index commutes coefficientwise through Corr for every charge, polynomial and correction shift. The proof establishes partial_pairDerivation and partial_insertion on the actual correction polynomial, retaining the charged singleton and pair constants, and then passes through optionEquivLeft."))),
                DescribeRole.Theorem),
            Paragraph(Text("The singleton coefficient at source weight one is the actual negative charge pairing divided by two. The pair coefficients retain pairScalar and both halfBinomial factors. They are constants for the source partial derivative, not deleted terms. Corr_neutralPolynomialMode consumes this result with the original frequency-weighted derivative and the actual charge zero mode.")),
            Paragraph(Text("The owning Reg mirrors provide exact dependent-telescope readouts and compiled source equivalence bridges for the substantive commutator and correction identities. They do not provide completed four-slot Contract.Registration inhabitants: variation, sensitivity and observational-dependence evidence remain admission obligations. Consumed algebraic and support helpers are proof organization, not separate new mathematical content.")),
            Paragraph(Text("This is the classical twisted lattice current law in the native constructors, not a claim of literature novelty. The established FLM background and the existing normal-support source attribution remain in force. Full all-state twisted Jacobi, the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives remain open.")))));
}
