using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickQuadraticEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual quadratic infimum equals its integrated maximal hockey reference exactly at the common-interior commutator criterion.",
        H("Integrated quadratic equality for singular finite pairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-hockey-quadratic-integrated-equality"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality."
                        + "quadratic_integrated_eq_iff_commute"),
                H("The actual infimum and the original matrix pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite positive semidefinite pair A,B, put S=A+B, "
                        + "C=normalize(S,A) and P=interiorProjection(C). The infimum over "
                        + "all actual finite reverse tests for f_*(s)=(s-1)^2/(s+1) "
                        + "equals quadraticHockeyValue exactly when PSP commutes with PCP. "
                        + "The proof uses the actual spectral test, the exact compact "
                        + "hockey integral, positivity and continuity of its gap, and "
                        + "original_all_thresholds_iff_commute. Singular, zero and empty "
                        + "matrix spaces are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-vanishing-curvature-gaps"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality."
                        + "vanishing_curvature_gaps_imply_commute"),
                H("Actual approximate tests transfer to the quadratic reference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any sequence of actual finite reverse tests, integrable gaps "
                        + "whose integrals tend to zero against a locally finite measure "
                        + "positive on every nonempty open set force the same original "
                        + "common-interior commutator to vanish. Pointwise gap convergence "
                        + "and dominated convergence on (0,1) transfer the costs to the "
                        + "actual quadratic minimum. This theorem assumes the vanishing "
                        + "gap integrals explicitly. It does not establish the general "
                        + "convex Stieltjes representation, its finite-cost approximation, "
                        + "or the full all-convex divergence equality classification."))),
                DescribeRole.Theorem))));
}
