using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class RationalCapacityTailRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/RationalCapacityTailRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational tail fillings produce every extended nonnegative total reading.",
        H("Rational Capacity Tail Realization"),
        Blocks(
            Paragraph(Text("Let g be a row of positive natural denominators and A a row of natural capacities. A total state has natural coordinates x_n at most A_n; a finite state additionally has finite support. The finite reading is the sum of x_n/g_n, and the extended total reading is the supremum of the inclusive partial sums through N. The chapter's denominator row is g_n = fib(n+2).")),
            Describe.Lean(
                DescribeId.Create("cofinal-capacity-rational-tail-filling"),
                DeclarationHandle.Create(Prefix + "cofinal_capacity_rational_tail_filling"),
                H("Exact rational tails and infinite tail mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose one positive real threshold epsilon works for every positive modulus d and every cutoff N: some index n greater than N has d dividing g_n and A_n/g_n at least epsilon. Then every nonnegative rational q is the exact reading of a finite legal state supported strictly after N. Split q into k equal rational parts a/b at most epsilon, choose k distinct suitable indices, and put a(g_n/b) at each selected coordinate. Conversely, exact rational filling alone forces every tail capacity sum to be infinite, since the tail dominates finite states with arbitrarily large integer readings."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-tail-filling-full-range"),
                DeclarationHandle.Create(Prefix + "rational_tail_filling_full_range"),
                H("Every extended nonnegative reading"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every nonnegative rational fills every tail exactly, the total reading maps the space of total capacity states onto the extended nonnegative reals. For a finite target, take increasing nonnegative rational approximations starting at zero. Fill each increment beyond the preceding finite support and a successively increasing cutoff. The resulting finite states increase coordinatewise and each coordinate eventually stabilizes. Their stabilized total state has all partial sums bounded by the target, while its total dominates every approximating reading, so equality follows. For infinity, take the capacity corner: its total dominates an infinite tail mass. The resulting state may have infinite support."))),
                DescribeRole.Theorem))));
}
