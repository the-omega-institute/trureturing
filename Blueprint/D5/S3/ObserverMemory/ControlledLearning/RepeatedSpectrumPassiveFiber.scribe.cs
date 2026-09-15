using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ControlledLearning;

internal sealed class RepeatedSpectrumPassiveFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated positive spectra have an exact commutant fiber for two passive learning steps.",
        H("Repeated-spectrum passive observation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-step-outputs-iff-commuting-difference"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ControlledLearning/RepeatedSpectrumPassiveFiber."
                    + "two_step_outputs_iff_commuting_difference"),
                H("Complete two-step output fiber, including resonance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a finite real diagonal matrix with positive diagonal entries. "
                        + "Consider two pairs of symmetric external Gram blocks, the same S as "
                        + "initial output, and nonzero step sizes eta and tau. Each step is the "
                        + "exact simultaneous gradient-descent recurrence for the fixed loss "
                        + "one half of the squared Frobenius norm of the two-layer output. "
                        + "The first and second outputs agree exactly when there is a symmetric "
                        + "X with A2=A1+X, B2=B1-X, X S=S X, and D X commuting with the first "
                        + "output, where D=I-eta-squared S-squared.")),
                    Paragraph(Text(
                        "The live proof extracts the full first-step difference from symmetric "
                        + "matrix entries. Positivity of the sum of two diagonal entries forces "
                        + "the two block differences to be opposite; the same equations then "
                        + "force commutation with S. Transport through the actual first step "
                        + "gives D X and minus D X, so the second output detects precisely their "
                        + "commutator with the observed first output. No distinct-eigenvalue "
                        + "assumption or inverse of D is used. Repeated eigenvalues and erased "
                        + "resonant directions are included.")),
                    Paragraph(Text(
                        "The declaration classifies symmetric-block recurrences. "
                        + "Physical Gram states additionally require positivity and a width "
                        + "rank bound. Those realization conditions, the generic four-step "
                        + "theorem, resonance collapse and quantitative prediction results "
                        + "are separate ordinary proofs in the accompanying theory. This "
                        + "document does not assert their Lean verification."))),
                DescribeRole.Theorem)),
        []));
}
