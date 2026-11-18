using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiBKMPathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual noncommuting matrix relative entropy is the weighted integral of its BKM resolvent form.",
        H("Umegaki divergence along a positive matrix segment"), Blocks(
            Describe.Lean(DescribeId.Create("reindex-logderiv"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiBKMPath.reindex_logDeriv"),
                H("Reindexing the logarithmic derivative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An equivalence between two finite carriers relabels both matrix indices as a real star-algebra equivalence. Applying it to logDeriv(Z,H) gives the logarithmic derivative with both Z and H relabeled, for arbitrary complex matrices Z and H. The continuous linear equivalence passes through the Bochner integral, and relabeling preserves each inverse and product in the resolvent integrand."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-positive-floor"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiBKMPath.common_floor"),
                H("A common positive spectral floor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n and positive definite complex matrices A and B on Fin n, there exists a real c strictly greater than zero such that c times the identity is at most A and at most B in the matrix order. Dimension zero is included. The proof takes the minimum of two positive spectral floors, with the empty carrier handled directly. The BKM path proofs and the actual faithful density-pair construction use this common floor."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("logderiv-continuous-on-floor"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiBKMPath.continuousOn_logDeriv_of_floor"),
                H("Continuity on an arbitrary set with a uniform floor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, arbitrary complex matrices B and H on Fin n, any set s of real numbers and any real c strictly greater than zero, assume c times the identity is at most B+tH for every t in s. Then t mapped to the actual matrix-valued Bochner logarithmic derivative logDeriv(B+tH,H) is continuous on s. No interval shape, nonemptiness of s or separate Hermitian hypothesis on B and H is imposed. The common resolvent majorant norm(H)/(c+u) squared supplies dominated continuity. This original helper is used by the path identity and, for fixed positive flag weight, by the faithful density-pair local expansion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("relative-entropy-bkm-path"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiBKMPath.relativeEntropy_eq_integral_bkm"),
                H("The path identity with the trace correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural dimension n, let A and B be positive definite complex matrices on Fin n, H=A-B, and Z(t)=B+tH. The real trace of A(log A-log B), minus the real trace of A-B, equals the integral from zero to one of (1-t) times Re Tr(H logDeriv(Z(t),H)). Here logDeriv is the actual matrix-valued Bochner integral of (Z+uI) inverse times H times (Z+uI) inverse over positive u. No commutation, common eigenbasis, trace normalization, Hessian identity or derivative formula is assumed. Fin n ranges over every finite reference dimension, including zero.")),
                    Paragraph(Text("The original affine-log derivative in AudenaertBinaryHolevoBound and the original trace-entropy derivative in TraceEntropyCalculus are applied directly. The resolvent representation and logarithmic directional derivative are standard ingredients of Audenaert's Quantum Skew Divergence. This assembly is repository-derived and makes no literature-priority claim.")),
                    Paragraph(Text("Positive spectral floors for A and B give a common positive floor c along the closed segment. The norm of the two-resolvent sandwich is bounded by the integrable function norm(H)/(c+u) squared. Shifted inverse differentiability gives pointwise continuity without choosing eigenvectors along the path; dominated convergence then gives continuity of the matrix-valued logDeriv and of its real trace pairing. The first derivative of F(t)=Re Tr(Z(t)log Z(t)) is G(t)=Re Tr(H(log Z(t)+I)), and G has derivative Q(t)=Re Tr(H logDeriv(Z(t),H)). Scalar FTC gives the integral of G, and integration by parts with weight 1-t gives the stated identity. Endpoint continuity is proved on the closed interval; two-sided derivatives are used only in its interior.")),
                    Paragraph(Text("For equal traces the correction Re Tr(A-B) is zero by linearity, in particular for normalized density states. Positive definiteness is essential to this delivered scope; no singular endpoint limit is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-bkm-integrable"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiBKMPath.weighted_bkm_integrable"),
                H("Integrability of the weighted BKM path"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive definite complex A and B on Fin n, the real trace of (A-B) times the logarithmic derivative at B+t(A-B) in direction A-B, weighted by 1-t, is interval integrable on [0,1]. The faithful conditional proof transports this integrability to arbitrary finite carriers for the joint and marginal paths."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conditional-block-bkm-path"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiBKMPath.conditional_relativeEntropy_eq_integral_bkm"),
                H("The conditional block-family identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let the block labels form any nonempty finite type, and let each A_i and B_i be a positive definite complex matrix on Fin n. Put A_R=sum_i A_i and B_R=sum_i B_i. The sum of the block Umegaki expressions minus the Umegaki expression of the totals equals the integral from zero to one of (1-t) times the sum of their BKM forms minus the BKM form of the totals. The reference blocks may be arbitrary noncommuting matrices. Neither blockwise equal traces nor total normalization is required.")),
                    Paragraph(Text("The totals are positive definite because the family is nonempty. Each weighted BKM form is integrable by the common-floor continuity argument. Finite-sum and subtraction rules for interval integrals therefore apply to the actual functions. The sum of the individual trace corrections is exactly the trace correction of the totals, so they cancel. This is the finite classical-label, arbitrary finite quantum-reference conditional expression.")),
                    Paragraph(Text("This bridge serves the Umegaki complete-versus-conditional question in Hirche, George, Nuradha and Wilde, arXiv:2608.27171v1, Definition 2 and section 9. It does not determine a contraction coefficient, prove coefficient equality, or establish strict separation. It assumes no sharp binary inequality or rare-corner lower bound."))),
                DescribeRole.Theorem))));
}
