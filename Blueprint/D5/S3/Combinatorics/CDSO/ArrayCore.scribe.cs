using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CDSO;

internal sealed class ArrayCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CDSO/ArrayCore.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual incidence arrays and the common-tail producer for CDSO Lemmas 13.4–13.5.",
        H("CDSO actual-array core remainder"),
        Blocks(
            Paragraph(Text(
                "One nonnegative normalized law on every nonempty subset supplies all marginals, cardinalities and energies. "
                + "For every tied-allowed smallest tail, the private implementation derives nonnegative actual-incidence residuals, "
                + "their sum Q(L), the actual-core Jensen gap and the exact lower certificate. "
                + "LocalizationBootstrap imports this implementation on its live proof path; no producer certificate is an input assumption.")),
            Describe.Lean(
                DescribeId.Create("cdso-array-data"),
                DeclarationHandle.Create(Prefix + "JointArray"),
                H("One actual finite incidence array"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "JointArray preserves the original law on all nonempty subsets, normalization, nonnegative masses, positive actual marginals, "
                    + "and the single actual expectation EK=a. No separate marginal vector, support condition, independence premise, certificate, "
                    + "near-minimizer premise, or graph condition is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cdso-producer-target"),
                DeclarationHandle.Create(Prefix + "Lemma134ProducerStatement"),
                H("Actual common-tail producer target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The full producer statement includes delta≤p≤u≤hp, the core rank bounds, the nonnegative discrete remainder Q, "
                    + "the nonnegative actual-core Jensen gap, and d≥H_D−u A_a(u)+E Q(L)+S_f under a²≥3h(2a+1). "
                    + "The implementation obtains the remainder by summing nonnegative actual-incidence residuals. A rational tangent inequality supplies Jensen; "
                    + "no producer certificate is added to the hypotheses of the localization theorem."))),
                DescribeRole.Definition)),
        []));
}
