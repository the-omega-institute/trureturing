using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanOneSidedIntegerDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Analytic/NymanOneSidedInteger";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A signed rational criterion for the Riemann hypothesis",
        H("A signed rational criterion for the Riemann hypothesis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-sided-signal-of-integer"),
                DeclarationHandle.Create(Owner + ".one_sided_signal_of_integer"),
                H("One-sided bounds from reciprocal integer scales"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose the real kernel W vanishes outside (1, 2) and is Lipschitz with constant K ≥ 0. If c times the shell sample at 1/N is at most C N^β for every positive natural N with C, β ≥ 0, then c times the logarithmic shell signal is eventually at most (C + 10 |c| K) exp(βt). The scale lies between two adjacent reciprocal integers, giving a uniform additive loss before the exponential factor is applied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-one-sided-original"),
                DeclarationHandle.Create(Owner + ".rh_iff_one_sided_original"),
                H("Equivalence with a fixed one-sided square-root bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each fixed real c ≠ 0, RH holds exactly when for every ε > 0 there is a C ≥ 0 such that c times the original finite rational scalar is at most C N^(1/2+ε) at every positive natural N. Taking c = 1 gives the upper bound and taking c = −1 gives the lower bound. The kernel's nonvanishing Mellin transform in the right half-strip makes the one-sided continuation detect every zero there. Under RH the absolute-value bound gives the signed bound after multiplying its constant by |c|."))),
                DescribeRole.Theorem))));
}
