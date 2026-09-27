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
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k >= 2, let p = parryParameter k and pi = parryLaw k. First, for every "
                    + "natural G and state s, the total variation between the G-step row of kernel k p and pi is "
                    + "at most (3/4)^(G/3). Second, for every natural n,G with n+G >= 2, the normalized complete "
                    + "complement-twisted prefix law differs from the pi-weighted stationary prefix law by at most "
                    + "2(n+G)(3/4)^(G/3) + Real.goldenRatio^(2-(n+G)). Third, for every natural R >= 1, G >= 1, "
                    + "and deterministic table f : (Fin R -> Bool) -> Bool, the absolute difference between the "
                    + "twisted and stationary probabilities of the same defect event is bounded by "
                    + "2(R+1+G)(3/4)^(G/3) + Real.goldenRatio^(2-(R+1+G)). The event is "
                    + "f(r_1,...,r_R) XOR f(r_0,...,r_(R-1)) XOR NOT r_R, with all relation bits taken "
                    + "from the same complete R+1-transition prefix and the same fixed table f used in both laws. "
                    + "Here G/3 is division rounded down, and the golden-ratio exponents are integers. "
                    + "No small-error premise is assumed."))),
                DescribeRole.Theorem))));
}
