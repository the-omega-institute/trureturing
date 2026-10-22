using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockOriginalTranslationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original All-State Physical Translation.",
        H("Original All-State Physical Translation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffockoriginaltranslation-ytw-translation-physical"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation.Ytw_translation_physical"),
                H("Physical derivative covariance for literal source translation and full corrected Ytw"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original source translation and original full corrected native Ytw satisfy Ytw(Ta)[E]=(E+2)/2 Ytw(a)[E+2] on every original finite charged oscillator source, every finite complex target tensor and every integer E. The sole native hypothesis is the original determinant-unit condition; charges, natural rank including zero, signature and oscillator occupations are unrestricted. The derivative is d/dz=(1/(2x))d/dx for z=x^2. T, oscillatorDerivation, chargePolynomial, Corr, Ytw, current, chargeScalar and the actual ground operator are not replaced.")),
                    Paragraph(Text("The charged base is established by genuine differentiation of the existing halfCreationExponential, signed coefficient recurrence, the actual minus-one-half first-descendant correction and finite target-polynomial/tensor extension. For arbitrary oscillator sources, the original finite Corr sector-translation recurrence is consumed. Its pair insertion derivations cancel the pair part of the correction connection; its charge-weighted singleton correction retains minus chargeNorm/2. Evaluation through the existing normalPolynomial and shiftLinear intertwines the remaining polynomial connection with the proved physical normal-insertion product law. Sparse polynomial induction covers empty and repeated words, and source linear induction covers all finite charge support. All infinite-mode manipulations occur only in previously established actual finite-support sums; no cancellation-raised nested-tail order bounds individual summands."))),
                DescribeRole.Theorem),
            Paragraph(Text("This covariance theorem and the inherited locality increments do not prove the full twisted Jacobi/module law, a complete moonshine construction, string theory or AdS/CFT. Those goals remain open. The owning Reg mirror gives a full source/target dependent coefficient-readout equivalence. It is not a declared_validated four-slot registration: enrolled-template variation, sensitivity, observational dependence and lawful application/source selection remain explicit admission obligations. Compilation and canonical emission do not substitute for source-owner admission or remote delivery.")))));
}
