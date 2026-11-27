using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanFixedScalarUpperDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Analytic/NymanFixedScalarUpper";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact finite rational criterion for the Riemann hypothesis",
        H("An exact finite rational criterion for the Riemann hypothesis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar-growth-of-zero-free"),
                DeclarationHandle.Create(Owner + ".scalar_growth_of_zero_free"),
                H("Scalar growth from a zero-free half-plane"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 1/2 ≤ θ < 1, nonvanishing of zeta on Re(s) > θ away from 1 gives a bound by C N^(θ+ε) at every positive natural N for every ε > 0. Summation by parts writes the weighted scalar in terms of ordinary Möbius prefix differences and increments of the kernel. Each increment is at most a Lipschitz constant divided by N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-scalar"),
                DeclarationHandle.Create(Owner + ".rh_iff_scalar"),
                H("Equivalence with square-root growth"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Riemann hypothesis holds exactly when, for every ε > 0, the finite rational scalar has absolute value at most C N^(1/2+ε) for some nonnegative C and all positive natural N. The forward direction uses the ordinary Möbius prefix estimate at θ = 1/2 and the reverse direction uses the Mellin product."))),
                DescribeRole.Theorem))));
}
