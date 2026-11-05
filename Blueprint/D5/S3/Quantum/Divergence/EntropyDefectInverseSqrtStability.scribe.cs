using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class EntropyDefectInverseSqrtStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual quantum entropy loss bounds supported inverse-square-root intertwining in L2.",
        H("Entropy defect and inverse-square-root stability"), Blocks(
            Describe.Lean(
                DescribeId.Create("entropy-defect-inverse-sqrt-stability"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/EntropyDefectInverseSqrtStability.entropy_defect_inverse_sqrt_stability"),
                H("A fourth-root L2 estimate on the actual supported model"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("Let Phi be a channel between arbitrary finite nonempty quantum systems, "
                    + "and let rho and sigma be density states with support of rho contained in support of sigma. "
                    + "Form their canonical supported relative-modular model M, with matrices A and B, map V and "
                    + "normalized vectors xi and eta. For every positive real m with mI <= A and mI <= B, set d "
                    + "to cfc(1/sqrt)(A) xi minus V cfc(1/sqrt)(B) eta. The square root of the real part of "
                    + "star(d) dot d is at most 4/(pi sqrt(m)) times Delta to the power one quarter, where Delta "
                    + "is the actual finite trace-log relative entropy of rho and sigma minus that of their "
                    + "channel images. The floor assumptions concern the supported carriers; the physical "
                    + "density states may be singular.")),
                    Paragraph(Text("The proof consumes the full positive-axis entropy resolvent energy budget. "
                    + "Mathlib's positive-power integrand gives the inverse-power integral after "
                    + "division by the positive spectral value. Substitution t=x/(1-x), the Beta integral and "
                    + "Gamma reflection evaluate the normalizer as pi/sin(pi alpha), giving pi at alpha=1/2. "
                    + "Finite spectral sums give the inverse-power identity and Bochner integrability; linear maps transfer them "
                    + "through V and the equivalence to EuclideanSpace Complex. All subsequent norms are L2. "
                    + "The positive semidefinite difference I minus V adjoint V gives contraction. Quadratic "
                    + "coercivity under the common spectral floor and Cauchy-Schwarz bound each resolvent "
                    + "vector by 1/m, hence their difference by 2/m. Splitting the weighted integral at a "
                    + "positive cutoff a gives 4 sqrt(a)/m plus sqrt(Delta)/sqrt(a), before division by pi. "
                    + "For positive Delta, choose a=m sqrt(Delta)/4. If Delta is zero, nonnegative energy "
                    + "vanishes almost everywhere and the integral error is exactly zero.")),
                    Paragraph(Text("The scalar integral and near/tail estimates are consumed helpers. This is "
                    + "a repository derivation using existing suppliers and pinned Mathlib analysis, with no "
                    + "claim of literature novelty. Identifying d with a physical Hilbert-Schmidt error "
                    + "requires additional spectral weights and a support-column projection; this theorem "
                    + "makes no such identification and asserts no trace-distance recovery estimate."))),
                DescribeRole.Theorem))));
}
