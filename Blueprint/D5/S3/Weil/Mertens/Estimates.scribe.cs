using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class EstimatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact weighted residual separates prime terms from all remaining Mangoldt terms.",
        H("Weighted nonprime residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-nonprime-residual-split"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/Estimates.E₁Λ.sub_E₁p_eq_sum_nonprime"),
                H("The original real-endpoint finite split"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real x, the original difference Mertens.E1Lambda(x)-Mertens.E1p(x) "
                        + "is sum(if n is not prime then Lambda(n)/n else 0,0<n<=floorNat(x)). "
                        + "The logarithmic terms cancel and Lambda(p)=log(p) at each prime p. "
                        + "The cutoff is inclusive, so a prime power equal to x remains present. "
                        + "No lower bound on x is needed.")),
                    Paragraph(Text(
                        "The same finite identity gives the nonprime partial sums in the weighted "
                        + "prime-limit argument and the selected-prime-power lower bound in the "
                        + "explicit Mertens envelope."))),
                DescribeRole.Theorem)),
        []));
}
