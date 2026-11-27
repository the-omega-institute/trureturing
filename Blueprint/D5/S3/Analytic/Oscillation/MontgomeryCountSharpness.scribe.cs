using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryCountSharpnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/MontgomeryCountSharpness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single commensurate spectrum attains the counting upper coefficient inside a fixed logarithmic band.",
        H("Sharpness of the counting bound in a logarithmic band"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-sharp-count-discrepancy"),
                DeclarationHandle.Create(Owner + ".exists_sharp_count_discrepancy"),
                H("A spectrum reaching the upper coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There are one locally finite positive spectrum of bounded two-term count discrepancy and a fixed A > 1 with the following property. For each ε > 0 and all sufficiently large Y, the normalized ordered pair sum is at most 2πc²+ε at every real phase. Some phase in (log Y,A log Y) also gives a normalized sum greater than 2πc²−ε. Here c = 1/(2π) and the normalization is Y(log Y)².")),
                    Paragraph(Text("Choose a phase from the progression of the commensurate spectrum with bounded count error. Its positive weighted sine sum reaches the total weight, so each sine in the inclusive cutoff is one and every difference cosine is one. Use the finite Cauchy energy bound with the real multiplicities as coefficients and with buffer radius √Y. The enlarged interval has length Y+2√Y and the retained mass fraction 2 arctan(√Y)/π tends to one. Together with the normalized count, this yields the matching lower coefficient.")),
                    Paragraph(Text("This construction shows that a strict cap below 2πc² on every fixed logarithmic band requires information beyond the stated count discrepancy. The construction concerns a general spectrum. The strict cap for the actual zeta ordinates remains a separate arithmetic question."))),
                DescribeRole.Theorem))));
}
