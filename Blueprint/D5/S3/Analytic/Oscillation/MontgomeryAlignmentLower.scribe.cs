using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryAlignmentLowerDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/MontgomeryAlignmentLower";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact phase alignment turns the leading count into a lower bound for the ordered pair sum.",
        H("The Cauchy lower coefficient at exact phase alignment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventually-montgomery-gt-of-phase-alignment"),
                DeclarationHandle.Create(Owner + ".eventually_montgomery_gt_of_phase_alignment"),
                H("A lower coefficient for fully aligned cutoffs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let N(Y) be the inclusive multiplicity-weighted count with N(Y)/(Y log Y) tending to c = 1/(2π). For each κ < 2πc² and all sufficiently large Y, any real t for which every pair through Y satisfies cos(t(γ−γ′)) = 1 has an ordered Lorentz pair sum strictly greater than κY(log Y)². The condition holds at zero frequency and whenever all individual phases agree modulo 2π.")),
                    Paragraph(Text("With each difference cosine equal to one, use the positive multiplicities as coefficients and apply the Cauchy lower bound on the buffered interval with radius √Y. The retained fraction 2 arctan(√Y)/π tends to one, and the normalized buffer length tends to one. The normalized count then gives the limiting lower coefficient."))),
                DescribeRole.Theorem))));
}
