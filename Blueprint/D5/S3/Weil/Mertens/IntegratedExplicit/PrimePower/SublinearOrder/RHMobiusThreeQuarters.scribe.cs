using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusThreeQuartersDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusThreeQuarters";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-quarter exponent for the signed RH prime window",
        H("Balance the damped degree prefix against the high-frequency tail"),
        Blocks(
        Describe.Lean(DescribeId.Create("rh-mobius-prime-window-three-quarters"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_three_quarters_of_rh"),
            H("The signed prime-window bound with arbitrary exponent slack"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("RH denotes Mathlib RiemannHypothesis. The window discrepancy is the integral of "
                    + "max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a). The tail primeTail(x) integrates "
                    + "(θ(t)−t)/t² over t>x, where θ(t) sums log p over primes p≤t.")),
                Paragraph(Text("The ordinary and root primitives use actual zeta-zero occurrences with analytic "
                    + "multiplicity. The residual subtracts their prescribed signed differences, with the strict "
                    + "retained condition 2n<m+1, and the signed arithmetic correction over 3≤n≤m.")),
                Paragraph(Text("Write q=m+1 and η=min(ε/3,1/12). The ordinary Möbius prefix exponent 1/2+η controls the "
                    + "arithmetic and near-range terms. The normalized omitted density for u≥q has three costs: "
                    + "q^(1/2+η)(H+1)^(1/2+η), (H+1)^(1+η), and q H^(η−1/2).")),
                Paragraph(Text("Take H=floor(q^(1/2)). The upper bound for H+1 controls the first two costs. The lower "
                    + "bound H≥q^(1/2)/2 controls the negative power. They are bounded by constants times "
                    + "q^(3/4+2η), independent of u.")),
                Paragraph(Text("Integrate the density against exp(−(1/2−1/q)u) between log a and log B. This gives the "
                    + "original endpoint gap for every allowed real pair a≤B, with value zero at equality."))),
            DescribeRole.Theorem))));
}
