using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickQuadraticIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite triangle integral represents the standard quadratic closed perspective and actual test cost.",
        H("The bounded quadratic hockey reference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-hockey-star-perspective-integral"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral."
                        + "star_perspective_hockey_integral"),
                H("Exact scalar reference, including both axes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For p,q >= 0, the standard perspective (p-q)^2/(p+q), with value "
                        + "zero at the origin, is q-3p plus eight times the integral of "
                        + "max(p-u(p+q),0) over 0 <= u <= 1. The proof integrates the "
                        + "linear triangle up to p/(p+q) and treats p=q=0 separately. "
                        + "This is the closed perspective of f_*(s)=(s-1)^2/(s+1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-star-actual-cost-integral"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral."
                        + "star_cost_hockey_integral"),
                H("The actual reverse-test cost identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Summing the scalar identity over the actual finite labels gives "
                        + "starCost = Tr B - 3 Tr A + 8 integral compactHockey. "
                        + "For 0<u<1, compactHockey is exactly (1-u) times the original "
                        + "classical hockey profile at t=u/(1-u). No improper integral "
                        + "or unproved identification with another cost is used."))),
                DescribeRole.Theorem))));
}
