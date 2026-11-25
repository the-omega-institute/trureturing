using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class FIBUnequalMarginalsDocument : IScribeDocumentDefinition
{
    private const string Result = "D5/S1/Words/AdmissibleWords/FIBUnequalMarginals.joint_range";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The joint range of two differences is an individual rectangle cut by one capacity.",
        H("Two event differences with unequal marginals"),
        Blocks(
            Describe.Lean(DescribeId.Create("unequal-joint-range"), DeclarationHandle.Create(Result),
                H("The exact region with five prescribed masses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Prescribe Lebesgue masses s, h, k, t and w for measurable subsets S, H, K, T "
                    + "and W of the half-open unit interval. Require S and W to lie in both H and K, "
                    + "and T to lie in K. The two differences W outside S and T outside H have masses "
                    + "a and b exactly when k is at most one, t is at most k, "
                    + "a lies between the maximum of zero and w minus s and the minimum of w and "
                    + "h minus s, b lies between the maximum of zero and t minus h and the minimum "
                    + "of t and one minus h, and a plus b is at most k minus s.")),
                    Paragraph(Text(
                    "The shared capacity bound gives the last inequality. For attainment choose "
                    + "the mass r of H intersect K as the maximum of s plus a, t minus b, and h plus k "
                    + "minus one. It is at most both h and k minus b. On the unit interval let K be "
                    + "the prefix of length k and choose H to occupy the prefix of length r together "
                    + "with the interval of length h minus r after K. Fit S and W into the prefix "
                    + "of length r with the required overlap. Fit the part of T in H into that "
                    + "prefix and place the remaining mass b immediately after it."))),
                DescribeRole.Theorem))));
}
