using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockChargedTranslationExtensionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Charged Translation on the Full Tensor Carrier.",
        H("Actual Charged Translation on the Full Tensor Carrier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffockchargedtranslationextension-charged-physical-translation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedTranslationExtension.charged_physical_translation"),
                H("Genuine charged physical derivative on every target tensor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every lattice with the original determinant-unit hypothesis and every charge, the full native charged field has physical derivative exactly equal to Ytw of the original source translation of the charged ground source. Every integer coefficient and every finite complex target polynomial/tensor are included, including natural rank zero. The proof extends the actual exponential differentiation from target ground tensors through the original charged-current coefficient law and Heisenberg creation commutator, then finite multivariate polynomial induction and tensor induction. Every integer-mode cut sum uses the original genuine finite-support theorem before a linear map, subtraction or singleton interchange. The first-descendant minus chargeNorm/2 correction restores the physical coefficient (E+2)/2, rather than a bare cover derivative."))),
                DescribeRole.Theorem),
            Paragraph(Text("The source here is the charged ground source, not an arbitrary oscillator source. The original Corr, all-state Ytw, source translation, current and ground implementations are unchanged. This endpoint supplies the charged base needed by the full source correction and normal-word calculus; it does not assert twisted Jacobi or completion of moonshine, string theory or AdS/CFT. The full-telescope Reg bridge is not declared_validated source admission: template variation, sensitivity, observational dependence and enrolled-template application/source selection still require evidence.")))));
}
