using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class RawCommonSeedFrontierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal four-exit family has an exact tradeoff between the worst expected row cost "
        + "and the expected maximum cost under one common seed.",
        H("Raw Common-Seed Frontier"),
        Blocks(Describe.Lean(
            DescribeId.Create("raw-common-seed-frontier"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/RawCommonSeedFrontier.result"),
            H("Attainment and domination of the entire frontier"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Fix a positive integer k, n = 8k + 16 and s = 5k + 1. A strategy "
                + "correctly decides membership in the third substitution image and terminates "
                + "on every finite input tree. Its cost is the number of distinct addresses "
                + "actually requested. The evaluation family consists of a baseline and the "
                + "four rows A, Y, H, Z at each of k slots.")),
                Paragraph(Text(
                "For every real t between zero and 1/s, choose the baseline-zero endpoint "
                + "with mass 1 - 5kt. At each slot choose the A-zero, H-two endpoint with "
                + "mass t, the Y-zero and Z-zero endpoints with mass t each, and the H-zero "
                + "endpoint with mass 2t. Every chosen endpoint is one actual globally correct "
                + "strategy, simultaneously attaining its menu vector on all rows. The "
                + "baseline's mean excess is 5kt and each other row's is 1 - t. Thus the "
                + "maximum expected row cost is n + 1 - t and the expected maximum under "
                + "the common seed is n + 1 + kt.")),
                Paragraph(Text(
                "At t = 1/s the baseline mass is also 1/s and every row's mean excess is "
                + "1 - 1/s. At t = 0 the baseline endpoint has maximum cost n + 1. Every "
                + "globally correct deterministic strategy has maximum cost at least n + 1.")),
                Paragraph(Text(
                "The comparison includes arbitrary probability spaces and arbitrary "
                + "input-independent selections of globally correct strategies whose row "
                + "costs are measurable. Expectations may be infinite. Enumerate the finite "
                + "menu once and choose the first endpoint dominated by each observed cost "
                + "vector. The resulting selection is measurable and lowers each row cost "
                + "and the maximum for each seed. If q is its second-kind mass, the "
                + "projected expected maximum is n + 1 + q. Averaging the A rows gives "
                + "r >= n + 1 - q/k. Averaging the 3k + 1 other rows gives "
                + "r >= n + 1 - (1 - 2q)/(3k + 1). These bounds meet at q = k/s. "
                + "For q at most k/s choose t = q/k; above that threshold choose t = 1/s. "
                + "The resulting attained pair is no larger in either coordinate than the "
                + "original law. Since the first coordinate strictly decreases and the "
                + "second strictly increases along this segment, it is the complete "
                + "frontier of nondominated pairs."))),
            DescribeRole.Theorem))));
}
