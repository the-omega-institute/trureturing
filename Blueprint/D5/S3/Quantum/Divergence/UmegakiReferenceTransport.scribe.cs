using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiReferenceTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial trace, amplification and trace pairing for the actual finite channel action.",
        H("Reference transport for conditional Umegaki divergence"), Blocks(
            Describe.Lean(DescribeId.Create("partialtraceright-posdef"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_posDef"),
                H("Faithfulness under partial trace"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite Z on a finite reference times a nonempty finite local carrier, the ordinary partial trace is positive definite. It is the sum of positive definite principal blocks. The reference center, residual identity and faithful state pairs use this fact."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partialtraceright-mul-embed"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_mul_embed"),
                H("Right reference multiplication under partial trace"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary complex matrices Z and X, the partial trace of Z times X tensor I is P(Z) times X. This puts the endpoint direction in the kernel and transports the marginal arithmetic operator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partialtraceright-embed-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_embed_mul"),
                H("Left reference multiplication under partial trace"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The partial trace of (X tensor I) times Z is X times P(Z). This supplies the trace pairing and the left part of the marginal arithmetic operator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-embed-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.trace_embed_pair"),
                H("Complex trace adjunction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Tr((X tensor I) adjoint V) equals Tr(X adjoint P(V)) for arbitrary complex matrices, using the ordinary partial trace. This preserves the pairing on zero-partial-trace directions when the reference center is subtracted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("amp-kronecker"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_kronecker"),
                H("Amplification on an elementary tensor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a finite channel N and arbitrary complex X and Z on the reference and input, the amplification sends X tensor Z to X tensor N(Z). This computes the channel image of the identity in the positivity argument."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("amp-mono"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_mono"),
                H("Amplification preserves matrix order"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the canonical finite channel, input matrix order X ≤ Z implies the same order for their amplified images. This transports a strictly positive lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-floor"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.positive_floor"),
                H("Positive lower bound by the identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every positive definite complex matrix on a finite carrier dominates m times the identity for some real m > 0. On the empty carrier the proof chooses m = 1. Amplification uses this lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("amp-posdef"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_posDef"),
                H("Faithfulness under amplification"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If N(I) is positive definite, the amplified channel sends each positive definite joint Z to a positive definite matrix for every finite reference. The assertion includes correlated input and the empty reference. The inverse-form and density-state proofs use this implication."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("amp-mul-embed"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_mul_embed"),
                H("Right reference multiplication under amplification"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The amplification of Z times X tensor input identity equals the amplification of Z times X tensor output identity. The reference center and the output residual use this law on arbitrary complex matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("amp-embed-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_embed_mul"),
                H("Left reference multiplication under amplification"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The amplification of (X tensor input identity) times Z equals (X tensor output identity) times the amplification of Z. This supplies the other multiplication law for the output residual."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phir-trace-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.PhiR_trace_pair"),
                H("Bilinear trace pairing of the channel adjoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite nonempty input and output, every finite reference and arbitrary complex Y and Z, Tr(PhiR(Y) Z) equals Tr(Y amp(N,Z)). The canonical Kraus adjoint is paired with the actual channel action. This gives the channel energy defect and the conjugate-transpose pairing."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phir-hs-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiReferenceTransport.PhiR_hs_pair"),
                H("Hilbert–Schmidt pairing of the channel adjoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same carrier hypotheses, Tr(PhiR(Y) adjoint Z) equals Tr(Y adjoint amp(N,Z)). This pairs the chosen output inverse direction and its reference-centered form with the original input direction."))),
                DescribeRole.Theorem))));
}
