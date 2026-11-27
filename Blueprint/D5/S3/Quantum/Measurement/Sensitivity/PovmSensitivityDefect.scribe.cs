using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Sensitivity;

internal sealed class PovmSensitivityDefectDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/Sensitivity/PovmSensitivityDefect.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/celeri2026rugosity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact four-term sensitivity loss for a prescribed finite POVM.",
        H("Relative entropy sensitivity for a prescribed measurement"),
        Blocks(
            Theorem("povm-bkm-sensitivity-decomposition", "sensitivity_decomposition",
                "Four contributions to the loss",
                "At a full-rank state with positive outcome masses, weight the POVM effects "
                + "by their Born probability derivatives divided by their masses. Subtract "
                + "the squared readout slope divided by the score's second moment from the BKM cost. "
                + "The slope and the normalized term vanish at zero second moment. The loss "
                + "splits into a squared BKM "
                + "distance, a logarithmic-mean gap, a sum of positive POVM sandwiches, "
                + "and the squared residual of the classical score projection. The logarithmic-mean "
                + "gap controls one third of the squared Frobenius norm of the commutator "
                + "with the square root of the state."),
            Theorem("povm-reverse-kl-sensitivity", "reverseKL_decomposition",
                "Sensitivity for reverse relative entropy",
                "Use the centered score one minus the reference mass divided by the Born mass. "
                + "The score pairing gives the directional derivative of reverse relative "
                + "entropy. Its squared norm is Pearson chi-squared divergence. A point-mass "
                + "reference includes the flat-state outcome of the binary rugosity measurement."),
            Theorem("povm-forward-kl-sensitivity", "forwardKL_decomposition",
                "Sensitivity for forward relative entropy",
                "Use the log ratio of Born and reference masses centered by relative entropy. "
                + "With a positive reference distribution its squared norm is the relative "
                + "entropy variance. The same four terms account for the loss along "
                + "the affine Born curve."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);
}
