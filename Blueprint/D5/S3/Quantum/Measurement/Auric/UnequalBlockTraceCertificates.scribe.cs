using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class UnequalBlockTraceCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict-trace certificates for unequal rank caps",
        H("Direct and complementary entropy for strictly admissible traces"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-direct-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_direct_certificate"),
                H("Direct weights for strictly admissible traces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/gale1957networkflows")),
                Blocks(
                    Paragraph(Text("Let ℓⱼ = max(d − mⱼ, 0) and b = d − ∑ⱼ ℓⱼ, with ∑ⱼ ℓⱼ ≤ d. Assume ∑ⱼ τⱼ = d and 0 < τⱼ < d − ℓⱼ = min(d, mⱼ) for every row j. There are positive weights wⱼ summing to one whose masked proportional allocation has multiplicity-weighted row masses τⱼ in the original labels. This uses ℓᵢ copies of the column missing row i and b copies of the common column.")),
                    Paragraph(Text("For each column take the log of the sum of exp(uⱼ) over the allowed rows, where u is the vector of row prices. Sum these potentials with the column multiplicities and subtract ∑ⱼ τⱼuⱼ. The objective is invariant under adding a common constant to the prices. Testing the allowed vertices bounds it below by the price spread times the minimum strict row slack, the minimum of τⱼ and d − ℓⱼ − τⱼ over all rows. Fixing one price at zero makes the sublevel through the zero vector compact, so the continuous objective attains a global minimum.")),
                    Paragraph(Text("At the minimum the coordinate derivatives vanish. Each column derivative is the corresponding masked softmax entry. Normalizing exp(uⱼ) over all rows gives w, and the derivative equations give the prescribed row masses. The denominators stay positive even for a column type of multiplicity zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-is-greatest-direct"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_isGreatest_direct"),
                H("Direct spectral maximum for strictly admissible traces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a finite matrix carrier of dimension d, assume ∑ⱼ ℓⱼ ≤ d, ∑ⱼ τⱼ = d and 0 < τⱼ < d − ℓⱼ for each original label j. Sort the positive direct weights in nonincreasing order and permute the caps, traces and missing types with them. The ordered direct maximum gives diagonal attainment and an upper bound. Inverting the row permutation preserves the spectral sum and transports each cap and trace back to its original effect.")),
                    Paragraph(Text("The greatest value is the direct allocation value with the permuted deficits, the common multiplicity b and the sorted weights. The feasible spectral-value set uses the original caps and traces. A zero multiplicity gives an empty diagonal block."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-complement-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_complement_certificate"),
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
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_isGreatest_complement"),
                H("Complementary spectral maximum for strictly admissible traces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the same strict trace hypotheses on a finite matrix carrier, sort the positive row weights in nondecreasing order. The induced permutation of missing types makes their reciprocal scales nondecreasing. The common scale is at least every missing scale, so the ordered complementary maximum applies after relabeling. The induced column permutation fixes the common type and preserves each block multiplicity with its type.")),
                    Paragraph(Text("The greatest value is the clipped allocation value for the permuted deficits, the common multiplicity and the transported weights and scales. Inverting the row permutation recovers exactly the original labeled feasible spectral-value set. These maxima concern the three effects and their spectra under strict trace inequalities."))),
                DescribeRole.Theorem))));
}
