using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.WhiteBoxLossFiberLaw;

internal sealed class TwoAtomMatchingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative two-atom coding admits an exact square completion and a radial lower bound.",
        H("Two-Atom Coding Energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("code-energy-square-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_energy_excess_eq"),
                H("Code energy square completion"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("codeEnergy"), Sp, Minus, Sp, F.Id("radial"), Sp, Eq, Sp,
                    F.Id("residualSquare"), Sp, Plus, Sp, F.Id("correlationDefect"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a unit direction and a real signal amplitude, the excess of the " +
                    "nonnegative two-atom code energy over the radial baseline is the sum of " +
                    "a squared residual and a correlation defect weighted by the regularization " +
                    "parameter. The identity keeps both code coordinates and both dictionary " +
                    "atoms in the same expression."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-code-energy-radial-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.feasible_code_energy_lower_bound"),
                H("Every feasible code obeys the radial lower bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("codeEnergy"), Sp, Ge, Sp, F.Id("lambda"), Sp, F.Id("times"), Sp,
                    F.Id("norm"), Sp, Minus, Sp, F.Id("lambdaSquare"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the signal norm is at least the regularization parameter, every " +
                    "coordinatewise nonnegative code has energy at least the radial baseline. " +
                    "The conclusion follows from the nonnegative square and the Cauchy--Schwarz " +
                    "correlation defects."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("code-cost-radial-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_cost_radial_lower_bound"),
                H("The infimal code cost obeys the radial lower bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("codeCost"), Sp, Ge, Sp, F.Id("radial"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Taking the infimum over all feasible nonnegative two-coordinate codes " +
                    "preserves the radial lower bound. The zero code supplies a nonempty family, " +
                    "while the pointwise square-completion inequality supplies the common floor."))),
                DescribeRole.Theorem)
        )));
}
