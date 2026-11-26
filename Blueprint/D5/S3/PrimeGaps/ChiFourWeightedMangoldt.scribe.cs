using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class ChiFourWeightedMangoldtDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/PrimeGaps/ChiFourWeightedMangoldt.";
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite character convolution gives a uniform weighted Mangoldt estimate modulo four.",
        H("The quadratic character modulo four"),
        Blocks(
            Describe.Lean(DescribeId.Create("character-prefix"),
                DeclarationHandle.Create(Prefix + "sum_chi_four_prefix"),
                H("Character prefixes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of the character over the positive integers "
                    + "up to X is the parity of floor((X+1)/2). It therefore belongs to "
                    + "{0,1}. The same prefix identity is used in the two alternating "
                    + "divisor hyperbola estimates."))), DescribeRole.Theorem),
            Describe.Remark(DescribeId.Create("classical-character-estimate"),
                DeclarationHandle.Create(Prefix + "abs_weighted_mangoldt_sum_le_twelve"),
                H("The classical bounded character sum"),
                AssessedProvenance.FromLiterature(Apostol),
                Blocks(Paragraph(Text("Apostol, Introduction to Analytic Number Theory, "
                    + "Chapter 7, Dirichlet's theorem on primes in arithmetic progressions, "
                    + "uses boundedness of the sum chi(n)*Lambda(n)/n for a nonprincipal "
                    + "character in the proof of Theorem 7.3. For chi modulo four this "
                    + "is the classical O(1) statement. The locator for this intermediate "
                    + "step is Chapter 7; no separate lemma number or page is asserted. "
                    + "The explicit constant twelve and the finite-convolution derivation "
                    + "below are repo-derived quantitative details.")))),
            Describe.Lean(DescribeId.Create("weighted-mangoldt"),
                DeclarationHandle.Create(Prefix + "abs_weighted_mangoldt_sum_le_twelve"),
                H("A bounded signed Mangoldt sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Apostol),
                Blocks(
                    Paragraph(Text("The classical Leibniz formula, supplied by Mathlib's "
                        + "Real.tendsto_sum_pi_div_four, gives the natural-order limit "
                        + "pi/4. Alternating partial-sum bounds give the harmonic character "
                        + "tail at y at most 1/y. No unconditional summability of the "
                        + "unpaired harmonic character series is used.")),
                    Paragraph(Text("The logarithmic character sum is bounded using the "
                        + "decrease of log(t)/t for t at least three. Finite Dirichlet "
                        + "convolution expresses it as the weighted Mangoldt sum convolved "
                        + "with the harmonic character prefix. The tail estimate and the "
                        + "ordinary Chebyshev upper bound control the convolution error "
                        + "by six. Since pi/4 is at least two thirds, the signed weighted "
                        + "Mangoldt sum has absolute value at most twelve. This explicit "
                        + "bound and finite-convolution presentation are repo-derived; "
                        + "the underlying boundedness statement is classical."))),
                DescribeRole.Theorem))));
}
