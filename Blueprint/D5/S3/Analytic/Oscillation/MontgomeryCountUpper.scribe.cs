using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryCountUpperDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/MontgomeryCountUpper";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bounded error in the two-term ordinate count gives a uniform upper bound for the Montgomery pair sum.",
        H("Uniform Montgomery upper bound from the count"),
        Blocks(
            Paragraph(Text("Write c = 1/(2π) and M(Y) = cY(log(cY)−1). Let N(Y) count the positive ordinates through Y with their multiplicities. In G_Y(t), use every ordered pair through the same inclusive cutoff and the factor 4/(4+(γ_j−γ_k)²) times cos(t(γ_j−γ_k)).")),
            Describe.Lean(
                DescribeId.Create("count-asymptotic-of-bounded-discrepancy"),
                DeclarationHandle.Create(Owner + ".count_asymptotic_of_bounded_discrepancy"),
                H("The normalized count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If |N(Y)−M(Y)| is bounded for all sufficiently large Y, then N(Y)/(Y log Y) tends to c. Use the normalized count limit with mean scale log(Y)/(2π), then rescale the limit by c."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abs-pair-sum-le-of-local-discrepancy"),
                DeclarationHandle.Create(Owner + ".abs_pairSum_le_of_local_discrepancy"),
                H("A bound from the count through the cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix Y > 1 and 1 ≤ A ≤ Y. If |N(x)−M(x)| ≤ D for every x between A and Y, then |G_Y(t)| ≤ N(Y)(2πc log Y + N(A) + 2D + c) for every real t. The cutoff interval contains both count evaluations for every Lorentz superlevel interval. The triangle inequality and |cos| ≤ 1 bound the absolute sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pair-sum-le-of-bounded-discrepancy"),
                DeclarationHandle.Create(Owner + ".pairSum_le_of_bounded_discrepancy"),
                H("A uniform bound on the leading coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each ε > 0, the same counting hypothesis gives G_Y(t) ≤ (2πc²+ε)Y(log Y)² for all sufficiently large Y and all real t.")),
                    Paragraph(Text("Let the count error be bounded by D from a fixed A onward. For an interval of radius r centered at an ordinate through Y, bound the mass above A by a difference of inclusive counts. Move the lower cutoff left by 1/log Y, clamped at A, to include ordinates at the left endpoint. The contribution through A is at most N(A). The difference of the two smooth main terms is at most c log Y times the distance between the cutoffs. Integrate the mass estimate over the centered superlevel intervals of the Lorentz kernel to obtain a row bound of 2πc log Y + N(A) + 2D + c.")),
                    Paragraph(Text("Bound each cosine by one, then sum the row bound with the outer multiplicities. The normalized count makes the resulting leading coefficient 2πc²."))),
                DescribeRole.Theorem))));
}
