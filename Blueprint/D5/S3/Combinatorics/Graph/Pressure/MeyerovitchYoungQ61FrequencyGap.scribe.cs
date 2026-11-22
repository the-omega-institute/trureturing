using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Pressure;

internal sealed class MeyerovitchYoungQ61FrequencyGapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Pressure/MeyerovitchYoungQ61FrequencyGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The translation-frequency linear program can give the wrong threshold for the original game.",
        H("A frequency threshold gap for Meyerovitch–Young Question 6.1"),
        Blocks(
            Paragraph(Text(
                "At each horizon Alice chooses an edge word and Bob minimizes the sum of paired "
                + "edge costs over walks of that length. Both endpoints are free, as in equations "
                + "(5) and (6) of Meyerovitch and Young. Alice has one vertex with three loops "
                + "+, −, and ∗. Bob has two vertices and all four directed edges. "
                + "https://arxiv.org/html/2603.21449v1#S4.E6")),
            Paragraph(Text(
                "Write b = c + ρ/8 and ε = √2 − 4/3. The shifts on the three loops are "
                + "√2 − 1/2, −2/3, and (√2 − 1)/2. Their unclipped rewards are b, b, and "
                + "b − ρ. The matrix with shift t and reward w has first row (w + t/2, w + t/2) "
                + "and second row (w + 1 − t/2, w − t/2), with departure vertices indexing "
                + "rows and arrival vertices indexing columns.")),
            Describe.Lean(
                DescribeId.Create("matrix-minimum-centered"),
                DeclarationHandle.Create(Owner + "matrixMinimum_eq_centered"),
                H("The centered recurrence computes the matrix minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real c and ρ and every word, the fold starts at difference and average "
                    + "zero. Minimizing each new endpoint over the two departures clips the "
                    + "difference d + t into [0, 1] and adds w minus half the clipping distance "
                    + "to the average. The final difference is the actual difference of the "
                    + "two endpoint minima and belongs to [0, 1]. The free-endpoint score is "
                    + "the final average minus half that difference."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-block-loss"),
                DeclarationHandle.Create(Owner + "matrixMinimum_le_four_block"),
                H("Every complete four-letter block loses at least one toll"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For 0 ≤ ρ ≤ ε, every four-letter block gains at most 4b − ρ from any "
                        + "difference in [0, 1]. A star charges ρ. Otherwise the block contains "
                        + "++, −−, or +−+. On that segment the magnitude of the sum of shifts "
                        + "exceeds the maximum unit change in the clipped difference by at least "
                        + "2ε. Telescoping therefore gives a clipping loss of at least ε.")),
                    Paragraph(Text(
                        "The block ∗−+− from difference 1/2 attains 4b − ρ, since all four "
                        + "steps stay in the interval without clipping. For every word of length "
                        + "n, complete blocks give the upper bound nb − ρ⌊n/4⌋ on both the "
                        + "centered score and the free-endpoint score plus half the final "
                        + "difference."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("frequency-threshold-gap"),
                DeclarationHandle.Create(Owner + "frequency_threshold_gap"),
                H("The frequency optimum and original value straddle the threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real c and 0 < ρ ≤ ε, both graphs are primitive at length one "
                        + "and every Alice word is legal. If c and ρ lie in ℚ(√2), every matrix "
                        + "entry lies in ℚ(√2). The frequency LP requires nonnegative frequencies "
                        + "summing to one and zero mean shift. It has greatest reward b > c. "
                        + "A feasible optimizer places zero mass on the star and balances the "
                        + "plus and minus shifts in inverse proportion to their magnitudes.")),
                    Paragraph(Text(
                        "At every horizon the original maximin is attained and is bounded by "
                        + "nb − ρ⌊n/4⌋. The free-endpoint matrix minimum is superadditive under "
                        + "concatenation, so Fekete's lemma gives a real limit of the maximin "
                        + "divided by the horizon. The four-letter bound gives V ≤ c − ρ/8 < c.")),
                    Paragraph(Text(
                        "The same matrices have infinitely many reachable differences. Starting "
                        + "at zero, choose the star below 2/3 and minus otherwise. The resulting "
                        + "words stay within a rotation interval and never clip. Distinct lengths "
                        + "give distinct differences because the interval length is irrational "
                        + "and the minus shift is rational and nonzero. The construction and "
                        + "bounds are those of equations (13)–(21) and the rotation in §5.1 of "
                        + "the three-matrix derivation."))),
                DescribeRole.Theorem))));
}
