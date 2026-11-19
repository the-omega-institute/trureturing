using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiKernelContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform endpoint estimate implies the arithmetic inverse-form estimate at every parameter.",
        H("Endpoint contraction on the partial-trace kernel"), Blocks(
            Describe.Lean(DescribeId.Create("arithmetic-positive"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.arithmetic_positive"),
                H("Positivity of the arithmetic operator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive semidefinite base and t in [0,1], the Hilbert–Schmidt arithmetic interpolation is positive. This applies to singular bases and supplies the range argument for the supported Moore–Penrose form."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("arithmetic"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.arithmetic"),
                H("Arithmetic interpolation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite square complex matrices Z and X and real u, this is (1-u) ZX + u XZ in the original matrix coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inversematrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.inverseMatrix"),
                H("Coordinates of the native inverse"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Transport V to the Hilbert–Schmidt carrier, apply the continuous-linear-map inverse of the native arithmetic operator at Z and u, and transport back. The cancellation laws below supply invertibility under their stated hypotheses."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("q"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.q"),
                H("Native inverse quadratic form"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take the real part of the Hilbert–Schmidt pairing of V with its image under the same native inverse."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("energy"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.energy"),
                H("Arithmetic energy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The energy of X is the real trace of X adjoint times arithmetic(Z,X,u)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("arithmetic-inversematrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.arithmetic_inverseMatrix"),
                H("Left inverse cancellation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If Z is positive definite and u lies in [0,1], applying arithmetic at Z to inverseMatrix(Z,V,u) recovers the arbitrary complex V. This cancels the marginal inverse in the residual and identifies the output inverse direction in the kernel estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inversematrix-arithmetic"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.inverseMatrix_arithmetic"),
                H("Right inverse cancellation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same positivity and interval hypotheses, inverseMatrix applied to arithmetic(Z,X,u) recovers X. This supplies the endpoint computation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-eq-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_eq_trace"),
                H("Trace of the inverse form"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary Z, V and real u, q is the real trace of V adjoint times inverseMatrix(Z,V,u). The identity uses the native trace pairing and also applies where the inverse is totalized. The residual computation uses this trace identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-zero-parameter"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_zero_parameter"),
                H("The ordinary inverse at the left endpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z and arbitrary complex V, q(Z,V,0) equals Re Tr(V adjoint Z inverse V). The kernel proof substitutes this equality for the input direction constructed from the reference center."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("energy-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.energy_nonneg"),
                H("Nonnegative arithmetic energy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive semidefinite Z and u in [0,1], the energy of any complex X is nonnegative. The endpoint trace test and inverse nonnegativity use this bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-eq-energy-inverse"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_eq_energy_inverse"),
                H("Energy of the inverse direction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z and u in [0,1], q(Z,V,u) is the energy of inverseMatrix(Z,V,u). The residual, weighted Cauchy–Schwarz, and kernel proofs use this equality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_nonneg"),
                H("Nonnegative inverse form"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z and u in [0,1], q is nonnegative for any complex V. The kernel proof applies this to both input and output before handling zero and positive cases."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-cauchy"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.weighted_cauchy"),
                H("Weighted Cauchy–Schwarz"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z, u in [0,1], and arbitrary complex matrices X and V, the square of Re Tr(X adjoint V) is at most energy(Z,X,u) times q(Z,V,u). The kernel proof uses the same inequality with the centered and uncentered adjoints."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("q-sub-arithmetic"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_sub_arithmetic"),
                H("Expansion after subtracting an arithmetic image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z, u in [0,1], and arbitrary complex H and X, the inverse form of H minus arithmetic(Z,X,u) equals q(Z,H,u) minus twice Re Tr(X adjoint H) plus energy(Z,X,u). This is the expansion used in the joint-minus-marginal residual identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partialtraceright-posdef"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_posDef"),
                H("Faithfulness under partial trace"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z on a finite reference times a nonempty finite local carrier, the ordinary partial trace is positive definite. It is the sum of positive definite principal blocks. The reference center, residual identity and faithful state pairs use this fact."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partialtraceright-mul-embed"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_mul_embed"),
                H("Right reference multiplication under partial trace"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary complex matrices Z and X, the partial trace of Z times X tensor I is P(Z) times X. This puts the endpoint direction in the kernel and transports the marginal arithmetic operator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partialtraceright-embed-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_embed_mul"),
                H("Left reference multiplication under partial trace"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The partial trace of (X tensor I) times Z is X times P(Z). This supplies the trace pairing and the left part of the marginal arithmetic operator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-embed-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.trace_embed_pair"),
                H("Complex trace adjunction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Tr((X tensor I) adjoint V) equals Tr(X adjoint P(V)) for arbitrary complex matrices, using the ordinary partial trace. This preserves the pairing on zero-partial-trace directions when the reference center is subtracted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("amp-mul-embed"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_mul_embed"),
                H("Right reference multiplication under amplification"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The right module law is amp(N, Z · (X ⊗ I_a)) = amp(N, Z) · (X ⊗ I_b). The reference center and the output residual use this law on arbitrary complex matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("amp-embed-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_embed_mul"),
                H("Left reference multiplication under amplification"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The amplification of (X tensor input identity) times Z equals (X tensor output identity) times the amplification of Z. This supplies the other multiplication law for the output residual."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phir-trace-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.PhiR_trace_pair"),
                H("Bilinear trace pairing of the channel adjoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite nonempty input and output, every finite reference and arbitrary complex Y and Z, Tr(PhiR(Y) Z) equals Tr(Y amp(N,Z)). The canonical Kraus adjoint is paired with the actual channel action. This gives the channel energy defect and the conjugate-transpose pairing."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phir-hs-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.PhiR_hs_pair"),
                H("Hilbert–Schmidt pairing of the channel adjoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same carrier hypotheses, Tr(PhiR(Y) adjoint Z) equals Tr(Y adjoint amp(N,Z)). This pairs the chosen output inverse direction and its reference-centered form with the original input direction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("endpointbound"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.EndpointBound"),
                H("The uniform left-endpoint premise"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a canonical finite channel N and coefficient c, quantify over every finite reference and every pair Z,V of complex joint matrices with Z positive definite and ordinary partial trace of V zero. The amplified left-endpoint inverse form is at most c times the input form. The inverse at zero pairs V with Z inverse V."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kernel-contraction"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiKernelContraction.kernel_contraction"),
                H("Arithmetic inverse contraction on the kernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let N be a canonical finite channel between nonempty carriers with N(I) positive definite. Let 0 ≤ c ≤ 1 and assume EndpointBound(N,c). For every finite reference, correlated positive definite Z, complex V with zero ordinary partial trace, and u in [0,1], q(amp(N,Z),amp(N,V),u) ≤ c q(Z,V,u). The reference may be empty.")),
                    Paragraph(Text("For c < 1, take the endpoint reference center X = (PZ) inverse P(Z PhiR(Y)). The direction Z times (PhiR(Y) minus X tensor I) has zero partial trace. The endpoint inequality and weighted Cauchy–Schwarz bound the centered energy by k times the channel defect, where k = c/(1-c). This gives a universal trace test for the common-state scalarizer.")),
                    Paragraph(Text("The scalarizer supplies one state and both residual Gram bounds. With p the input inverse form, q the output inverse form, f the uncentered input energy and d = q-f, the two pairings bound q squared by f p and k d p. For q > 0 their combination yields (1+k)q ≤ k p. The proof handles q = 0 before cancellation, includes c = 0, and at c = 1 uses the uncentered bound and d ≥ 0.")),
                    Paragraph(Text("The faithful density-state theorem applies this estimate to the actual joint-minus-marginal residual. Its premise requires a uniform endpoint bound for all references and complex kernel directions. The supported extension applies the faithful theorem to output-regularized channels and proves the coefficient equality for arbitrary finite channels."))),
                DescribeRole.Theorem))));
}
