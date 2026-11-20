using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PrincipalPlaquetteBlockBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent rows strengthen the one-party plaquette obstruction for native paired channels.",
        H("Coherent block budget for the one-party plaquette obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rt-native-coherent-matrix-unit-row"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget."
                    + "matrixUnit_row_square_le"),
                H("One squared diamond budget per coefficient row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A tagged rank-one test chooses the column amplitude vector proportional "
                    + "to all the errors in the row. It bounds their squared norm sum by "
                    + "the square of the native unhalved diamond distance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rt-native-coherent-plaquette-budget"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget."
                    + "paired_improved_one_party_native_diamond"),
                H("Improved one-party phase bound from coherent rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For one selected pair of fibres the two row tests give a Frobenius "
                        + "budget. The opposite gauge converts entry errors into signed real "
                        + "budget deficits; a reciprocal variance identity then strengthens "
                        + "the cosine obstruction by a factor of the square root of two.")),
                    Paragraph(Text(
                        "Only the first party's phase is used. The native paired-channel "
                        + "identity, labelled fibres and original target coefficients remain "
                        + "hypotheses. No assumption on leakage, common quotient or "
                        + "cross-entry dominance is added."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rt-native-zero-plaquette-coherent-floor"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget."
                    + "paired_sharp_zero_plaquette_native_diamond"),
                H("Zero-phase obstruction from the coherent sum and both row budgets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When the first-party plaquette has zero phase, its gauged entries "
                        + "are nonnegative real. The flat rank-one test controls the signed "
                        + "sum of the four errors as well as the two row tests controlling "
                        + "their squared sum. A square-root inequality combines these "
                        + "budgets to give the square root of two minus one as a lower bound.")),
                    Paragraph(Text(
                        "The formal theorem is a lower bound for a specified pair, not "
                        + "a guarantee that such a pair exists in the unrestricted problem. "
                        + "Attainment is not formalized here.")),
                    Paragraph(Text(
                        "For comparison, a paper-level calibrated four-fibre example attains "
                        + "the bound. Set k to the square root of two minus one. Let u and v "
                        + "be unit vectors with real inner product minus k, and take fibre "
                        + "directions u, v, i u, i v. Each fibre has the orthonormal records "
                        + "formed by the sum and difference of its direction with a shared "
                        + "orthogonal unit vector, normalized by the square root of two. "
                        + "Use conjugate records on the other side. The selected first-side "
                        + "cross block has strictly positive entries.")),
                    Paragraph(Text(
                        "In the per-fibre symmetric and antisymmetric bases, the Hermitian "
                        + "coefficient error is k times the direct sum of the four-cycle "
                        + "adjacency and a two-edge matching adjacency. Its absolute value "
                        + "has every original diagonal fibre block equal to k times the "
                        + "two-dimensional identity. The uniform input gives the normalized "
                        + "trace norm k, and the absolute-value dual majorant gives the "
                        + "matching upper bound in the calibrated trace-norm formula. "
                        + "The exact fixture and its semantics are not Lean claims here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rt-native-signed-plaquette-quarter-sector"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget."
                    + "paired_quarter_plaquette_native_diamond"),
                H("A strict quarter obstruction on a first-party phase sector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When the first-party quarter-angle cosine is at least 0.899228, "
                        + "the unhalved native diamond error is strictly greater than a "
                        + "quarter. A pair of flat rank-one inputs with equal and alternating "
                        + "signs controls the real and imaginary parts of the gauge-projected "
                        + "error sum. The row-square budget and the two contraction sums "
                        + "then rule out the entire closed quarter sublevel.")),
                    Paragraph(Text(
                        "The bound applies to the selected fibre pair, with the same paired "
                        + "dilation, labels and target as before. It neither establishes that "
                        + "one of the pairs must have this phase nor settles recovery for "
                        + "unrestricted channels.")),
                    Paragraph(Text(
                        "The isolated two-fibre estimate cannot simply be continued to all "
                        + "phases. A calibrated example has cosine p = 2/sqrt(5) and diamond "
                        + "error exactly 1/4. In the following paper construction, J is the "
                        + "all-ones matrix, S is the alternating-sign matrix, and q is "
                        + "the square root of 1 minus p squared. The first cross block is "
                        + "(p J + i q S)/(2p), and the error block is "
                        + "(J + i S)/8. The second cross block is obtained "
                        + "by entrywise dividing the target minus this error by the first "
                        + "block. In the symmetric and antisymmetric bases the cross blocks "
                        + "have eigenvalues (1, i/2) and (1, -i). Adjoining identity diagonal "
                        + "blocks realizes "
                        + "them as calibrated Grams.")),
                    Paragraph(Text(
                        "The flat input gives the lower bound 1/4 for this example. The "
                        + "complete calibrated Hermitian error has operator norm 1/4, so "
                        + "the identity times 1/4 is a matching trace-norm dual majorant. "
                        + "These matrix identities were checked exactly; the example "
                        + "is not a formalized counterexample for the four-fibre model."))),
                DescribeRole.Theorem))));
}
