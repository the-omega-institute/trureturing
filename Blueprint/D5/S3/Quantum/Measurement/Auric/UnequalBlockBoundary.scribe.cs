using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class UnequalBlockBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projection rigidity and exact entropy on closed trace faces",
        H("Unequal rank caps at zero and saturated traces"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("effect-eq-zero-of-trace-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary.effect_eq_zero_of_trace_zero"),
                H("Zero trace forces a zero effect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On a finite complex matrix carrier, a positive semidefinite matrix with zero real trace is zero. Its trace is real by positivity, so the positive semidefinite trace-zero criterion applies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("effect-sq-eq-self-of-trace-cap"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary.effect_sq_eq_self_of_trace_cap"),
                H("Trace saturation forces a projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let A be a positive semidefinite complex d by d matrix with A ≤ I and rank at most m. If its real trace equals min(d, m), then A² = A. The nonzero eigenvalues are in [0, 1] and their number is at most min(d, m). Their deficits from one have sum zero, so each nonzero eigenvalue equals one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projection-mul-effect-eq-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary.projection_mul_effect_eq_zero"),
                H("A projection annihilates each positive summand of its complement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let P be a finite complex Hermitian matrix with P² = P. Suppose B and C are positive semidefinite and B + C = I − P. Then PB = BP = 0. On the range of P the two nonnegative quadratic forms sum to zero. The positive semidefinite quadratic-form criterion gives BP = 0, and taking adjoints gives PB = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projection-row-reduces"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary.projection_row_reduces"),
                H("Reduction to a binary effect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take three positive semidefinite complex matrices A summing to identity and pairwise distinct labels j, i and k. If Aⱼ² = Aⱼ, then Aᵢ + Aₖ = I − Aⱼ and both products of Aⱼ with either remaining effect vanish, in either order. In addition Aᵢ and Aₖ commute, since Aₖ = I − Aⱼ − Aᵢ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("commute-on-boundary"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary.commute_on_boundary"),
                H("Every feasible tuple on a closed trace face commutes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For three positive semidefinite complex effects summing to identity in dimension d, let mᵣ be their rank caps and τᵣ their prescribed real traces. If some row j has τⱼ = 0 or τⱼ = min(d, mⱼ), every pair of effects commutes. The distinguished row is a projection in either case, with the zero matrix allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectral-sum-eq-complement-on-boundary"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary.spectralSum_eq_complement_on_boundary"),
                H("Equality of direct and complementary spectral sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take a feasible tuple of three positive semidefinite complex effects summing to identity, with real traces τᵣ and rank caps mᵣ. Let j, i and k be pairwise distinct, and suppose τⱼ = 0 or τⱼ = min(d, mⱼ). With h(x) = −x log x, the sum of h(x) over all three spectra equals the sum of h(1 − x) over the same spectra.")),
                    Paragraph(Text("In a common eigenbasis the columns are either the projection column (1, 0, 0) or binary columns (0, x, 1 − x), in the order j, i, k. Both spectral sums give zero on projection columns and binary entropy on the other columns."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("saturated-face-maximum"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary.saturated_face_maximum"),
                H("Common attained maximum at a saturated row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let d be the finite carrier dimension, let mᵣ be the three rank caps and set Lᵣ = max(d − mᵣ, 0). Assume ∑ᵣ Lᵣ ≤ d, all real traces are nonnegative, and their sum is d. For pairwise distinct row labels j, i and k assume τⱼ = min(d, mⱼ).")),
                    Paragraph(Text("The common greatest direct and complementary spectral value is Lⱼ H₂(τᵢ/Lⱼ), where H₂ is binary entropy. Both objectives agree on every feasible tuple, their common value never exceeds this number, and a single feasible tuple attains it for both. An empty complement gives value zero.")),
                    Paragraph(Text("The projection has exactly Lⱼ complementary coordinates. Jensen bounds their entropy using the total mass τᵢ. In the diagonal construction, the column missing j splits that mass uniformly, and row j occupies every other column type. The two remaining rank caps each allow the whole complement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-row-face-maximum"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary.zero_row_face_maximum"),
                H("Common attained maximum at a zero row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let d be the finite carrier dimension, let mᵣ be the three rank caps and set Lᵣ = max(d − mᵣ, 0). Assume ∑ᵣ Lᵣ ≤ d, each real trace satisfies 0 ≤ τᵣ ≤ min(d, mᵣ), and their sum is d. For pairwise distinct row labels j, i and k assume τⱼ = 0. Set N = d − Lᵢ − Lₖ.")),
                    Paragraph(Text("The common greatest direct and complementary spectral value is N H₂((τᵢ − Lₖ)/N). Both objectives agree on every feasible tuple, their common value never exceeds this number, and a single feasible tuple attains it for both. When N = 0 the value is zero.")),
                    Paragraph(Text("Row i has at least Lᵢ zero eigenvalues. Because the remaining two effects sum to identity, the Lₖ zeros forced in row k supply at least Lₖ ones in row i. Remove disjoint slots of exactly these sizes and apply Jensen to mass τᵢ − Lₖ on the N remaining slots. The attaining diagonal effects put zeros and ones in the corresponding missing types and split uniformly across the type missing j and the common type."))),
                DescribeRole.Theorem))));
}
