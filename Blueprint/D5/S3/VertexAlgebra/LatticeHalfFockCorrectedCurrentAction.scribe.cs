using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCorrectedCurrentActionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Current commutation through the complete charged correction",
        H("Current commutation through the complete charged correction"),
        Blocks(
            Paragraph(Text("correctedPolynomial is the exact original all-state constructor: Corr followed by normalPolynomial and shiftLinear. All charges and every finite source polynomial remain in scope.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockcorrectedcurrentaction-corrected-polynomial-current-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCorrectedCurrentAction.correctedPolynomial_current_commutator"),
                H("Current commutation through the complete charged correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The proof applies the actual normal-polynomial commutator to each retained correction shift. Corr_neutralPolynomialMode proves that original source modes commute through the correction coefficients and that the corrected source support is contained in the original correction-shift support."))),
                DescribeRole.Theorem),
            Paragraph(Text("Before interchange, every correction coefficient uses the same finite original positive-mode range. The correction-shift support and the original mode range form a genuine finite common rectangle. Signed coverShift commutes with the original shiftLinear by an exact doubled-cover coefficient calculation. No cancellation-raised aggregate Hahn order is used as a bound on individual signed normal tuples.")),
            Paragraph(Text("The owning Reg mirrors provide exact dependent-telescope readouts and compiled source equivalence bridges for the substantive commutator and correction identities. They do not provide completed four-slot Contract.Registration inhabitants: variation, sensitivity and observational-dependence evidence remain admission obligations. Consumed algebraic and support helpers are proof organization, not separate new mathematical content.")),
            Paragraph(Text("This is the classical twisted lattice current law in the native constructors, not a claim of literature novelty. The established FLM background and the existing normal-support source attribution remain in force. Full all-state twisted Jacobi, the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives remain open.")))));
}
