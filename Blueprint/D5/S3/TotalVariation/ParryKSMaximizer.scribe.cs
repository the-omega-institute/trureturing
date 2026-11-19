using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryKSMaximizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rigidity of entropy maximization for the bilateral forbidden-run shift.",
        H("The bilateral Parry law is the unique entropy maximizer"),
        Blocks(Describe.Lean(
            DescribeId.Create("bilateral-parry-ks-maximizer"),
            DeclarationHandle.Create("D5/S3/TotalVariation/ParryKSMaximizer.bilateral_parry_maximizer"),
            H("Equality in the bilateral Parry entropy bound"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every forbidden-run length k at least two, take a bilateral coding with "
                    + "the nearest-zero suffix property and a probability with the stationary "
                    + "Parry suffix cylinders at every integer origin. For each probability "
                    + "preserved by the unsigned shift, its full Kolmogorov–Sinai entropy is at "
                    + "most minus log p. Equality holds exactly when it equals the stated Parry "
                    + "probability. Here p is the reciprocal Perron root.")),
                Paragraph(Text(
                    "For every nonempty finite history, compare its actual joint mass with the "
                    + "mass given by its history marginal followed by one Parry transition. "
                    + "Stationarity cancels the expected endpoint log weights, so the relative "
                    + "entropy equals the difference between minus log p and the entropy "
                    + "increment. Forgetting the earliest suffix cannot increase this relative "
                    + "entropy. Each such difference therefore bounds the deficit in the full "
                    + "entropy rate from below.")),
                Paragraph(Text(
                    "At equality the finite relative entropies all vanish, fixing the law of "
                    + "the next suffix after every history. Each positive suffix has a unique "
                    + "possible predecessor, so stationarity and normalization determine the "
                    + "initial marginal. The common marginal and transitions determine all "
                    + "suffix cylinders. Each Boolean bit is recovered from its next suffix, "
                    + "and the bilateral Boolean cylinders determine the full measure."))),
            DescribeRole.Theorem))));
}
