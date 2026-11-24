using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class UnequalBlockEffectsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attained spectral entropy with unequal rank caps",
        H("Three effects with unequal missing dimensions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-greatest-direct"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_direct"),
                H("Attained maximum for normalized weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/gale1957networkflows")),
                Blocks(
                    Paragraph(Text("Take three complex positive semidefinite effects that sum to identity on a finite carrier of dimension d. Each effect has rank at most its own cap mⱼ and real trace τⱼ. Put ℓⱼ = max(d − mⱼ, 0), assume their sum is at most d, and let b be the difference. For positive normalized weights w₀ ≥ w₁ ≥ w₂, put wⱼ on the common column and wⱼ/(1 − wᵢ) on missing-type column i for each j ≠ i. The excluded row i is zero. The trace assumption requires τⱼ to be the weighted row mass with the stated multiplicities.")),
                    Paragraph(Text("The total of −x log x over the three spectra has a greatest value. It equals the sum of the scalar entropies of the missing-type columns with multiplicities ℓᵢ, plus b times the entropy of the common column. Diagonal effects realize the allocation.")),
                    Paragraph(Text("Gale's cut criterion characterizes feasibility of the scalar row masses on the allowed row–column connections. The spectral maximum here assumes the normalized weights and trace equations above.")),
                    Paragraph(Text("Select ℓⱼ zero eigenvectors of each effect. Pad the spans of successive prefixes to a nested flag, then take differences of its orthogonal projections. The diagonal overlaps of these layers in each effect eigenbasis give the weights for the scalar supporting lines. Each selected zero eigenvector has all its layer mass in its flag prefix, so the ordered intercepts bound the excluded contribution from below. The linear terms sum using the prescribed traces and the identity sum of the three effects. The bound allows arbitrary intersections among the original kernels and holds when a layer has zero dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("is-greatest-complement"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_complement"),
                H("Attained complementary entropy with ordered scales"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take three complex positive semidefinite effects that sum to identity in dimension d, with rank caps mⱼ and real traces τⱼ. Assume the missing dimensions ℓⱼ = max(d − mⱼ, 0) satisfy ∑ⱼ ℓⱼ ≤ d. The three missing types have multiplicities ℓⱼ and the common type has multiplicity d − ∑ⱼ ℓⱼ. The objective is the sum of φ(x) = −(1 − x) log(1 − x) over the three spectra.")),
                    Paragraph(Text("Fix a positive multiplier for each row and positive nondecreasing scales for the three missing column types and the common type. Each allowed entry is the maximum of zero and one minus the product of its row multiplier and column scale. An excluded entry is zero. Assume all four column-sum equations hold, with the sum of the three entries equal to one in each missing-type column and in the common column, including columns of multiplicity zero. The multiplicity-weighted row sums must equal the prescribed traces.")),
                    Paragraph(Text("The scalar allocation attains the greatest spectral sum. A supporting line at each allowed entry uses the logarithm of the product plus one as its slope. The zero cutoff supplies the supporting line at an endpoint, including for excluded entries when the product is at least one. Increasing column scales decrease the intercepts, which supplies the ordering used in the same projection argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("is-greatest-three-four-four"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.isGreatest_three_four_four"),
                H("Exact maximum for caps 3, 4, 4"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In dimension 5 take rank caps (3, 4, 4) and real traces (15/11, 20/11, 20/11). With φ(x) = −x log x and a = (√565 − 5)/18, the greatest total spectral entropy is 4φ(1/2) + 2[φ(a/(a+1)) + φ(1/(a+1))] + φ(a/(a+2)) + 2φ(1/(a+2)).")),
                    Paragraph(Text("The weights proportional to (a, 1, 1) give the required traces. The polynomial equation 9a² + 5a − 15 = 0 verifies the mass of the first row, and the other two masses are equal by symmetry. The layers have multiplicities 2, 1, 1 and 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-direct-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.exists_direct_certificate"),
                H("Direct weights for strictly admissible traces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let ℓⱼ = max(d − mⱼ, 0) and b = d − ∑ⱼ ℓⱼ, with ∑ⱼ ℓⱼ ≤ d. Assume ∑ⱼ τⱼ = d and 0 < τⱼ < d − ℓⱼ = min(d, mⱼ) for every row j. There are positive weights wⱼ summing to one whose masked proportional allocation has multiplicity-weighted row masses τⱼ in the original labels. This uses ℓᵢ copies of the column missing row i and b copies of the common column.")),
                    Paragraph(Text("For each column take the log of the sum of exp(uⱼ) over the allowed rows, where u is the vector of row prices. Sum these potentials with the column multiplicities and subtract ∑ⱼ τⱼuⱼ. The objective is invariant under adding a common constant to the prices. Testing the allowed vertices bounds it below by the price spread times the minimum strict row slack, the minimum of τⱼ and d − ℓⱼ − τⱼ over all rows. Fixing one price at zero makes the sublevel through the zero vector compact, so the continuous objective attains a global minimum.")),
                    Paragraph(Text("At the minimum the coordinate derivatives vanish. Each column derivative is the corresponding masked softmax entry. Normalizing exp(uⱼ) over all rows gives w, and the derivative equations give the prescribed row masses. The denominators stay positive even for a column type of multiplicity zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-is-greatest-direct"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.exists_isGreatest_direct"),
                H("Direct spectral maximum for strictly admissible traces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a finite matrix carrier of dimension d, assume ∑ⱼ ℓⱼ ≤ d, ∑ⱼ τⱼ = d and 0 < τⱼ < d − ℓⱼ for each original label j. Sort the positive direct weights in nonincreasing order and permute the caps, traces and missing types with them. The ordered direct maximum gives diagonal attainment and an upper bound. Inverting the row permutation preserves the spectral sum and transports each cap and trace back to its original effect.")),
                    Paragraph(Text("The greatest value is the direct allocation value with the permuted deficits, the common multiplicity b and the sorted weights. The feasible spectral-value set uses the original caps and traces. A zero multiplicity gives an empty diagonal block."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-complement-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.exists_complement_certificate"),
                H("Clipped weights and scales for strictly admissible traces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same strict row trace and dimension conditions, there are positive row weights wⱼ and positive column scales k_c. The allowed entry is max(0, 1 − wⱼk_c), and the excluded entry is zero. All four formal columns sum to one, including those of multiplicity zero. The multiplicity-weighted row masses equal τⱼ in the original labels.")),
                    Paragraph(Text("At prices u take wⱼ = exp(−uⱼ). For a missing type the scale is the reciprocal of the sum of the two allowed weights. For the common type, write S for the sum of all weights and M for their maximum. The scale is max(2/S, 1/(S − M)). This formula keeps the clipped allocation continuous through the cutoff. A common-column entry can vanish even under strict row trace inequalities.")),
                    Paragraph(Text("The column potential is the maximum over its allowed probability simplex of the complementary entropy plus the linear price term. The scalar supporting inequalities establish this maximum at the clipped allocation, and evaluating at a vertex yields the price lower bound used in compact minimization. Comparing scores at the minimizing prices and at nearby prices on either side of each coordinate gives the two opposite inequalities for the displaced row mass. Continuity gives equality with τⱼ at the minimum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-is-greatest-complement"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects.exists_isGreatest_complement"),
                H("Complementary spectral maximum for strictly admissible traces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the same strict trace hypotheses on a finite matrix carrier, sort the positive row weights in nondecreasing order. The induced permutation of missing types makes their reciprocal scales nondecreasing. The common scale is at least every missing scale, so the ordered complementary maximum applies after relabeling. The induced column permutation fixes the common type and preserves each block multiplicity with its type.")),
                    Paragraph(Text("The greatest value is the clipped allocation value for the permuted deficits, the common multiplicity and the transported weights and scales. Inverting the row permutation recovers exactly the original labeled feasible spectral-value set. These maxima concern the three effects and their spectra under strict trace inequalities."))),
                DescribeRole.Theorem))));
}
