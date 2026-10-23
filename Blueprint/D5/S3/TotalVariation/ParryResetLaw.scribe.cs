using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryResetLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParryResetLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stationary signed Parry law.",
        H("The stationary signed Parry law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parryresetlaw-suffix-weight-succ"),
                DeclarationHandle.Create(Prefix + "suffixWeight_succ"),
                H("Finite suffix recurrence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k:Nat, p:Real, j:Fin k and hj:j.val+1<k, suffixWeight k p j=p+p*suffixWeight k p (j.val+1). Splitting the finite geometric sum into its first term and tail proves the recurrence. It supports the stationary law and the right Perron weight of the original Reset beam trace."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parryresetlaw-suffix-weight-last"),
                DeclarationHandle.Create(Prefix + "suffixWeight_last"),
                H("Last suffix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k:Nat, p:Real, j:Fin k and hj:not(j.val+1<k), suffixWeight k p j=p. The remaining finite sum has length one. This is the terminal case of the stationary and Perron recurrences."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parryresetlaw-parry-stationary-law"),
                DeclarationHandle.Create(Prefix + "parry_stationary_law"),
                H("The stationary signed Parry law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k >= 2, set p = parryParameter k = (dbonacciPerronRoot k)^(-1), "
                    + "h_j = suffixWeight k p j, S = normalizer k, and pi(s) = parryLaw k s = "
                    + "p^(s.2.val) h_(s.2) / (2S). Then 1/2 < p <= Real.goldenRatio^(-1) and "
                    + "rootSum k p = sum over a in range k of p^(a+1) = 1. For every j in Fin k, "
                    + "p <= h_j <= 1, and S >= 1. Every entry of K = kernel k p is nonnegative, every row "
                    + "of K sums to one, and pi(s) >= 0 for every state s. The law is normalized, "
                    + "sum_s pi(s) = 1; it is stationary, with sum_s pi(s) K(s,t) = pi(t) for every t; "
                    + "and it is invariant under sign complement: pi(flip(s)) = pi(s) for every s."))),
                DescribeRole.Theorem))));
}
