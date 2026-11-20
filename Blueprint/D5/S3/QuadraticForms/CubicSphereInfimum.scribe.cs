using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class CubicSphereInfimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/CubicSphereInfimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mazhang2026scaleddowndate");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For h(t) = (3t − t³)/2 the infimum of R_h(x)² over unit vectors is 16(17 − 9√3)/23, never attained.",
        H("Sharp sphere bound for an increasing odd cubic"),
        Blocks(
            Describe.Lean(DescribeId.Create("cubic-def"),
                DeclarationHandle.Create(Prefix + "cubic"), H("The cubic"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("h(t) = (3t − t³)/2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rayleigh-def"),
                DeclarationHandle.Create(Prefix + "rayleigh"), H("The ratio R_h"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For x ∈ ℝᵈ, R_h(x) = Σᵢ xᵢ h(xᵢ) / (Σᵢ h(xᵢ)²)^{1/2}. Since h(0) = 0, summing over "
                    + "all coordinates agrees with the source's active-coordinate convention."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("infimum-value-def"),
                DeclarationHandle.Create(Prefix + "infimumValue"), H("The infimum value"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("c = 16(17 − 9√3)/23."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("large-mass-def"),
                DeclarationHandle.Create(Prefix + "largeMass"), H("The large squared coordinate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("a* = 6 − 3√3, a number in (0, 1)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("approach-def"),
                DeclarationHandle.Create(Prefix + "approach"), H("The minimizing sequence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The vector in ℝ^{m+1} with first coordinate √a* and m coordinates √((1 − a*)/m): one "
                    + "squared coordinate a* and m equal squared tail coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cubic-moment"),
                DeclarationHandle.Create(Prefix + "moment"), H("The moment identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every unit vector x, with pᵢ = xᵢ² and sₖ = Σᵢ pᵢᵏ, "
                        + "R_h(x)² = (3 − s₂)²/(9 − 6s₂ + s₃).")),
                    Paragraph(Text(
                        "Expand xᵢ h(xᵢ) = (3pᵢ − pᵢ²)/2 and h(xᵢ)² = (9pᵢ − 6pᵢ² + pᵢ³)/4 and use "
                        + "Σᵢ pᵢ = 1. This is equation (5) of H. Ma and W. Zhang (DOI 10.5281/zenodo.23920598)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cubic-sphere-infimum"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Infimum, non-attainment and the two-coordinate minimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "h is strictly increasing on [−1, 1], h(1) = 1, and h(t)/t is strictly decreasing "
                        + "for t > 0. Every unit vector x of every finite dimension, of any signs, satisfies "
                        + "c < R_h(x)², and c is the greatest lower bound of R_h(x)² over nonnegative unit "
                        + "vectors, so the infimum c = 16(17 − 9√3)/23 is never attained. The sequence with "
                        + "one squared coordinate a* = 6 − 3√3 and m equal squared tail coordinates consists of "
                        + "nonnegative unit vectors whose values R_h² tend to c. Every unit vector with at "
                        + "most two nonzero coordinates satisfies 80/81 ≤ R_h(x)², with equality exactly "
                        + "when 9s₂ = 7, and equality holds for a nonnegative vector in dimension two. The vector with squared coordinates "
                        + "(4/5, 1/10, 1/10) has R_h(x)² = 13689/13885 < 80/81.")),
                    Paragraph(Text(
                        "Put a = √s₂ ∈ (0, 1]. Each pᵢ ≤ a, so s₃ ≤ a s₂ = a³ and the moment identity gives "
                        + "R_h(x)² ≥ (3 − a²)²/(9 − 6a² + a³). The factorization 23(3 − a²)² − "
                        + "16(17 − 9√3)(9 − 6a² + a³) = (a − a*)²(23a² + (4 + 6√3)a + 12√3 − 15), with a "
                        + "positive second factor for a ≥ 0, gives R_h(x)² ≥ c. Equality would need "
                        + "s₃ = a s₂, which forces every positive pᵢ to equal a; then s₂ = a and s₂ = a², so "
                        + "a = 1 ≠ a*, a contradiction. Along the sequence s₂ → a*² and s₃ → a*³, so R_h² → c. "
                        + "On a support of at most two points 2s₃ = 3s₂ − 1, and then R_h(x)² − 80/81 = "
                        + "(9s₂ − 7)²/(81(9 − 6s₂ + s₃)); squared coordinates (3 ± √5)/6 give s₂ = 7/9. "
                        + "This is Theorem 11 of H. Ma and W. Zhang (DOI 10.5281/zenodo.23920598), answering "
                        + "Lucid's sphere question (Mathematics Stack Exchange 5146381) linked from "
                        + "MathOverflow 513954, revision 2."))),
                DescribeRole.Theorem))));
}
