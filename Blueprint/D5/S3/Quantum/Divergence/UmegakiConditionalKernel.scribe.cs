using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiConditionalKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse and energy identities used in the faithful conditional Umegaki estimate.",
        H("Matrix coordinates of the arithmetic inverse"), Blocks(
            Describe.Lean(DescribeId.Create("arithmetic"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic"),
                H("Arithmetic interpolation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite square complex matrices Z and X and real u, this is (1-u) ZX + u XZ in the original matrix coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inversematrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.inverseMatrix"),
                H("Coordinates of the native inverse"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Transport V to the Hilbert–Schmidt carrier, apply the continuous-linear-map inverse of the native arithmetic operator at Z and u, and transport back. The cancellation laws below supply invertibility under their stated hypotheses."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("q"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q"),
                H("Native inverse quadratic form"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take the real part of the Hilbert–Schmidt pairing of V with its image under the same native inverse."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("energy"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.energy"),
                H("Arithmetic energy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The energy of X is the real trace of X adjoint times arithmetic(Z,X,u)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("arithmetic-inverse-pairing-intervalintegrable"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic_inverse_pairing_intervalIntegrable"),
                H("Integrability of the inverse pairing"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite square complex Z and H with Z positive definite, the real inverse pairing of H is interval integrable on [0,1]. The finite spectral expansion and the integrable affine reciprocal terms justify the integration in the conditional BKM estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("arithmetic-inversematrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic_inverseMatrix"),
                H("Left inverse cancellation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If Z is positive definite and u lies in [0,1], applying arithmetic at Z to inverseMatrix(Z,V,u) recovers the arbitrary complex V. This cancels the marginal inverse in the residual and identifies the output inverse direction in the kernel estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inversematrix-arithmetic"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.inverseMatrix_arithmetic"),
                H("Right inverse cancellation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same positivity and interval hypotheses, inverseMatrix applied to arithmetic(Z,X,u) recovers X. This supplies the endpoint computation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-eq-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_eq_trace"),
                H("Trace of the inverse form"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary Z, V and real u, q is the real trace of V adjoint times inverseMatrix(Z,V,u). The identity uses the native trace pairing and also applies where the inverse is totalized. The residual computation uses this trace identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-zero-parameter"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_zero_parameter"),
                H("The ordinary inverse at the left endpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z and arbitrary complex V, q(Z,V,0) equals Re Tr(V adjoint Z inverse V). The kernel proof substitutes this equality for the input direction constructed from the reference center."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("energy-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.energy_nonneg"),
                H("Nonnegative arithmetic energy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive semidefinite Z and u in [0,1], the energy of any complex X is nonnegative. The endpoint trace test and inverse nonnegativity use this bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-eq-energy-inverse"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_eq_energy_inverse"),
                H("Energy of the inverse direction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z and u in [0,1], q(Z,V,u) is the energy of inverseMatrix(Z,V,u). The residual, weighted Cauchy–Schwarz, and kernel proofs use this equality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_nonneg"),
                H("Nonnegative inverse form"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z and u in [0,1], q is nonnegative for any complex V. The kernel proof applies this to both input and output before handling zero and positive cases."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-cauchy"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.weighted_cauchy"),
                H("Weighted Cauchy–Schwarz"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z, u in [0,1], and arbitrary complex matrices X and V, the square of Re Tr(X adjoint V) is at most energy(Z,X,u) times q(Z,V,u). The kernel proof uses the same inequality with the centered and uncentered adjoints."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-sub-arithmetic"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_sub_arithmetic"),
                H("Expansion after subtracting an arithmetic image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z, u in [0,1], and arbitrary complex H and X, the inverse form of H minus arithmetic(Z,X,u) equals q(Z,H,u) minus twice Re Tr(X adjoint H) plus energy(Z,X,u). This is the expansion used in the joint-minus-marginal residual identity."))),
                DescribeRole.Theorem))));
}
