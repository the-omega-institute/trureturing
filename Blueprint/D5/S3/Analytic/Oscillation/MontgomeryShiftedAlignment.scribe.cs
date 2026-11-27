using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryShiftedAlignmentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/MontgomeryShiftedAlignment";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shift of order inverse cutoff separates the multiplicity phase sum from Lorentz pair energy.",
        H("Phase cancellation near a commensurate return"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pair-sum-loss-of-aligned-shift"),
                DeclarationHandle.Create(Owner + ".pairSum_loss_of_aligned_shift"),
                H("Quadratic loss at complete pair alignment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let N(Y) count multiplicities through the inclusive cutoff Y. When every retained pair has difference cosine one at p, the loss in the ordered Lorentz pair sum from p to p+h lies between zero and 2h²N(Y)² for every real h.")),
                    Paragraph(Text("For a difference d, the cosine loss at the shifted phase is at most (dh)²/2. Multiplying by 4/(4+d²) bounds the contribution per unit pair weight by 2h². The ordered sum of multiplicity products is N(Y)²."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-commensurate-shift-with-phase-cancellation"),
                DeclarationHandle.Create(Owner + ".exists_commensurate_shift_with_phase_cancellation"),
                H("Cancellation and leading pair energy at the same frequency"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There is a single positive locally finite spectrum with bounded two-term counting discrepancy and aligned frequencies p(Y). At sufficiently large real cutoffs, p(Y) and p(Y)+2π/Y lie in one fixed logarithmic band. At the shifted frequency the modulus of the multiplicity phase sum divided by N(Y) tends to zero. The ordered Lorentz pair sum divided by Y(log Y)² tends to 2πc², where c = 1/(2π).")),
                    Paragraph(Text("Positivity forces every phase in the aligned sine sum to equal the same unit complex number. The shift tests the ordinates rescaled by Y with a character that completes one turn on the unit interval. For this smooth character, integration against the scaled inclusive count gives the uniform interval average, which is zero. The quadratic loss is bounded above by a constant times (log Y)², so it vanishes after normalization by Y(log Y)². The estimates for the aligned frequency and the uniform counting upper bound give the common limiting coefficient."))),
                DescribeRole.Theorem))));
}
