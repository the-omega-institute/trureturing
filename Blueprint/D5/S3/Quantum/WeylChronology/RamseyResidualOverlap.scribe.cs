using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class RamseyResidualOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/RamseyResidualOverlap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A supplied residual motional overlap damps the Ramsey fringe, and its distance from unit overlap certifies the probability-level closure error used by the robust chronology model.",
        H("Ramsey Residual-Overlap Closure"),
        Blocks(
            Paragraph(Text(
                "The physical interface multiplies the coherent Ramsey interference term by "
                    + "one supplied complex overlap. Unit overlap recovers the existing ideal "
                    + "fringe, contractive overlap preserves the probability interval, and the "
                    + "distance from unit overlap controls the existing closureError field.")),
            Paragraph(Text(
                "This module does not derive the overlap from the concrete Schrodinger "
                    + "displacement action. The current continuous Weyl owner intentionally "
                    + "does not yet provide an L2 inner product or coherent-state overlap. It "
                    + "also does not identify the repository's finite environment-record "
                    + "overlap model with continuous motional overlap.")),
            Describe.Lean(
                DescribeId.Create("overlap-fringe"),
                DeclarationHandle.Create(Prefix + "overlapRamseyFringe"),
                H("Residual-overlap Ramsey fringe"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The plus-port population is one half plus visibility over two times the "
                        + "real part of the residual overlap multiplied by the analyzer-adjusted "
                        + "phase."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unit-overlap"),
                DeclarationHandle.Create(Prefix + "overlap_ramsey_fringe_unit"),
                H("Unit overlap recovers the ideal contrast fringe"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At overlap one, the physical fringe is exactly the existing ideal Ramsey "
                        + "probability under affine visibility damping."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probability-range"),
                DeclarationHandle.Create(Prefix + "overlap_ramsey_fringe_mem_unit"),
                H("Contractive overlap gives a probability"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For visibility between zero and one and overlap norm at most one, the "
                        + "overlap-damped fringe lies in the unit interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("overlap-deviation"),
                DeclarationHandle.Create(Prefix + "overlap_ramsey_fringe_deviation_le"),
                H("Residual overlap controls fringe deviation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The absolute probability deviation from unit overlap is at most absolute "
                        + "visibility over two times the complex norm of overlap minus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chronology-fringe"),
                DeclarationHandle.Create(Prefix + "overlapChronologyFringe"),
                H("Golden chronology residual-overlap fringe"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The general overlap fringe is specialized to the pi-over-two analyzer and "
                        + "the existing phase twice coupling times magnusCenter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chronology-unit"),
                DeclarationHandle.Create(Prefix + "overlap_chronology_fringe_unit"),
                H("Unit overlap equals the existing visible chronology fringe"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At unit overlap, the specialized physical fringe is exactly the existing "
                        + "visibleChronologyFringe."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chronology-probability"),
                DeclarationHandle.Create(Prefix + "overlap_chronology_fringe_mem_unit"),
                H("Contractive chronology overlap remains probabilistic"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Physical visibility and contractive overlap keep the golden chronology "
                        + "fringe inside the probability interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closure-error"),
                DeclarationHandle.Create(Prefix + "overlapClosureError"),
                H("Overlap-derived closure residual"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The probability-level closure residual is the overlap chronology fringe "
                        + "minus its unit-overlap ideal fringe."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("closure-bound"),
                DeclarationHandle.Create(Prefix + "overlap_closure_error_le"),
                H("Complex overlap defect certifies closure error"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing closure residual is bounded by absolute visibility over two "
                        + "times the norm distance of the residual overlap from one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("calibration"),
                DeclarationHandle.Create(Prefix + "overlapCalibration"),
                H("Overlap-derived Ramsey calibration"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A one-acquisition calibration record uses ideal baseline, visibility, "
                        + "coupling and zero phase offset, with closureError supplied by the "
                        + "derived residual-overlap term."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("calibration-fringe"),
                DeclarationHandle.Create(Prefix + "robust_fringe_overlap_calibration"),
                H("The existing robust fringe equals the physical overlap fringe"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating the existing robustChronologyFringe on the overlap-derived "
                        + "calibration reproduces the physical overlap-damped fringe exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("calibration-budget"),
                DeclarationHandle.Create(Prefix + "overlap_calibration_budget_le"),
                H("The existing calibration budget inherits the overlap bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When nominal visibility and coupling equal the acquisition values, the "
                        + "existing calibration deviation budget reduces to the derived closure "
                        + "residual and is bounded by the complex overlap defect."))),
                DescribeRole.Theorem))));
}
