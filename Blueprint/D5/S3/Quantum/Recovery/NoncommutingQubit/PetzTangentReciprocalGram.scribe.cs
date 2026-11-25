using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.NoncommutingQubit;

internal sealed class PetzTangentReciprocalGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two parity sectors of the qubit tangent residual obey the common marginal-dependent reciprocal Gram bound.",
        H("Paired reciprocal Gram bounds for the Petz tangent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petztangentreciprocalgram-paired-parity-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound"),
                H("Combined reciprocal parity estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0<g≤1, 0<δ≤1, and real β with g²+β²=1, the squared modulus of g(a+b)+β(c+d) is bounded by 1+2/(1+δ²) times the sum of the two weighted reciprocal energies. For the arcsine functionals, the even coefficients are normalized by 1/x and the odd coefficients by 1/(x(x+g)), for nodes x in {1,δ}. The estimate allows arbitrary complex coefficients and the maximally mixed marginal δ=1.")),
                    Paragraph(Text("The odd Gram splits into a common even lower Gram and a positive correction with unsquared reciprocal nodes. The even estimate uses the square-root chord bound. Both sector estimates apply to the real and imaginary parts of the coefficients and retain the two-node cross terms.")),
                    Paragraph(Text("The physical common-reference tangent application requires the arcsine evaluations and substitution back to the affine spectral variable, followed by identification with the actual arithmetic BKM residual and ordinary Petz sandwich."))),
                DescribeRole.Theorem))));
}
