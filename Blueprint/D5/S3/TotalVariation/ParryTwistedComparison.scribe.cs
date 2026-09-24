using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryTwistedComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParryTwistedComparison.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual mixing and complete-prefix comparison.",
        H("Actual mixing and complete-prefix comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parrytwistedcomparison-parry-mixing-and-complete-prefix"),
                DeclarationHandle.Create(Prefix + "parry_mixing_and_complete_prefix"),
                H("Actual mixing and complete-prefix comparison"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the actual Parry kernel, the total variation between every G-step row and the actual stationary law is at most three quarters to the floor of G divided by three. Removing the common one-quarter mass produces a stochastic residual channel. Contraction on each three-step block and on the remaining steps yields the rate. For every complete prefix of n transitions with n plus G at least two, its normalized complement-twisted law differs from the actual stationary prefix law by at most 2(n + G) times this rate, plus the golden ratio to the integer power 2 - (n + G). No small-error assumption is used. The same bound applies to the absolute probability gap for the explicit defect event f(r_1,...,r_R) XOR f(r_0,...,r_(R-1)) XOR NOT r_R. Both probabilities use the same fixed deterministic table on the complete R+1-transition prefix."))),
                DescribeRole.Theorem))));
}
