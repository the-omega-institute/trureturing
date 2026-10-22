using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCorrectionTranslationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Native Correction Translation.",
        H("Finite Native Correction Translation"),
        Blocks(
            Paragraph(Text("The original Corr is retained. correctedSource only applies the inverse of optionEquivLeft to the existing correctionPolynomial; it is not another state-field or correction assignment. The differential connection acts on the shift variable t by -t^2 and on each source oscillator X(i,k) by (k+1)X(i,k+1), minus the actual charge-weighted pair insertions.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockcorrectiontranslation-corr-sector-translation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCorrectionTranslation.Corr_sectorTranslation"),
                H("Original Corr applied to original sector translation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every rank, charge and finite oscillator polynomial, Corr of the literal sectorTranslation equals the finite correction readout of the explicit differential connection plus the charge-weighted original insertions. The singleton recurrence retains halfBinomial 1=-1/2. The pair recurrence is proved for all positive source weights; the derivation commutator is checked on every original polynomial variable, then extended by the universal derivation property. The existing correctionWord permutation and monomial basis are consumed to identify actual Corr with insertion on arbitrary polynomials. Polynomial induction uses the literal oscillatorDerivation and chargePolynomial, not a translation operator defined by the wanted identity."))),
                DescribeRole.Theorem),
            Paragraph(Text("All operations in this correction theorem are finite polynomial operations. No infinite normal-mode interchange is claimed here. LatticeHalfFockOriginalTranslation joins this finite recurrence to the genuine charged physical derivative and the normal-polynomial evaluation laws. This correction theorem alone is not the all-state Ytw translation theorem or a twisted Jacobi certificate.")),
            Paragraph(Text("The Reg mirror proves the unrestricted dependent source/readout equivalence, including rank zero. Its typed obligations do not establish declared_validated source admission: lawful enrolled-template application, variation, sensitivity, observational dependence and source selection remain open.")))));
}
