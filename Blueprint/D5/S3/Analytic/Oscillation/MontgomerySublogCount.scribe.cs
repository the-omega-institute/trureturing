using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomerySublogCountDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/MontgomerySublogCount";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An error smaller than the logarithmic scale suffices for the leading upper coefficient.",
        H("Montgomery sums with sublogarithmic counting error"),
        Blocks(
            Paragraph(Text("Write c = 1/(2π) and M(Y) = cY(log(cY)−1). Let N(Y) count all multiplicities through the inclusive cutoff. Assume (N(Y)−M(Y))/log Y tends to zero.")),
            Describe.Lean(
                DescribeId.Create("count-asymptotic-of-sublog"),
                DeclarationHandle.Create(Owner + ".countAsymptotic_of_sublog"),
                H("The leading count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ratio N(Y)/(Y log Y) tends to c. The rescaled discrepancy tends to zero and the main term supplies the limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pair-sum-le-of-sublog-discrepancy"),
                DeclarationHandle.Create(Owner + ".pairSum_le_of_sublog_discrepancy"),
                H("A uniform leading upper coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every ε > 0 and all sufficiently large Y, the absolute value of the inclusive ordered Lorentz pair sum at every real phase parameter is at most (2πc²+ε)Y(log Y)².")),
                    Paragraph(Text("Given η > 0, choose A so that the absolute count error is at most η log Y at every height from A through Y. Apply the finite-cutoff count bound with D = η log Y. The two endpoint errors contribute at most 2η log Y to each row. The leading count converts the row bound into the uniform coefficient by taking η sufficiently small."))),
                DescribeRole.Theorem))));
}
