using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSlitChartGermsDocument : IScribeDocumentDefinition
{
    private const string FourPoint = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/";
    private const string Prefix = FourPoint + "OriginalFourMSlitChartGerms.";
    private const string Sector = FourPoint + "OriginalFourMSectorContinuation.";
    private const string Identity = FourPoint + "OriginalFourPointIdentityK.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit slit chart germs for the actual rank-24 four-point channels",
        H("Native cusp germs on the Euler slit"),
        Blocks(
            D("four-point-slit-iterate-channel", "slitChannelA", "The continued A channel",
                DescribeRole.Definition,
                Text("Project the slit charge-sector sums onto the diagonal with offset "
                    + "s − H − K + 1 at energy zero. Multiply each diagonal by (−t)^(−H−K) "
                    + "and sum the classes with the quadratic and Fourier signs. This is A "
                    + "as a function of its native parameter t. "),
                Ref(Sector + "slitChargeSector")),
            D("four-point-slit-direct-channel", "slitChannelB", "The continued B channel",
                DescribeRole.Definition,
                Text("In class b, sum the slit Laurent diagonals for Q, R, P over the native "
                    + "finite lowering cutoff. The term of order ℓ uses the detector lowered "
                    + "ℓ times, diagonal sum m + n + r + ℓ and the original lowering weight.")),
            D("four-point-slit-inverse-channel", "slitChannelD", "The continued D channel",
                DescribeRole.Definition,
                Text("Use the corresponding lowering sum for P, R, Q in the inverse parameter. "
                    + "The sector of class a has the quadratic sign of a + b.")),
            D("four-point-slit-chart-germs", "slitChartGerms", "Holomorphy and the actual cusp germs",
                DescribeRole.Theorem,
                Text("Assume a positive definite real Gram matrix, rank 24 and unit Gram "
                    + "determinant. Finite occupation projection preserves holomorphy of the "
                    + "continued charge-sector sums. On the opening disk the actual sewn "
                    + "diagonal at w and at −w equals the same slit diagonal at w². "
                    + "Their average is the actual numerator at −w² near zero. Substituting "
                    + "the complex square root of t, which tends to zero with t and squares "
                    + "to t, identifies the slit diagonal at t with the actual numerator at −t. "
                    + "The Laurent factor and the finite charge and lowering sums give "
                    + "holomorphy on the punctured slit and the punctured germs at t = 0. "
                    + "The A germ is actual A at −t, and the B and D germs are actual B and D at t. "),
                Ref(Sector + "slitChargeSector_differentiableOn"), Text(", "),
                Ref(Sector + "slitChargeTerm_eq_native"), Text(", "),
                Ref(FourPoint + "FourPointChannelCoefficients.actualDiagonalNumerator_spec")),
            D("four-point-identity-k-from-slit-crossing", "identityK_of_slitChart_crossing",
                "The mode identity conditional on the two slit crossing equalities",
                DescribeRole.Theorem,
                Text("Assume rank 24 and a positive definite real Gram matrix with unit "
                    + "determinant. For every output class, suppose A(1 − z⁻¹) = "
                    + "2¹² z^(m+n+r+2) B(z) accumulates at an interior point of the double slit. "
                    + "Suppose either A(1 − z⁻¹) = D(z⁻¹) accumulates at a point of U_A ∩ U_D, "
                    + "or 2¹² z^(m+n+r+2) B(z) = D(z⁻¹) accumulates at a point of U_B ∩ U_D. "
                    + "The explicit slit functions give holomorphy and punctured germs at native "
                    + "zero, with actual A at −t and actual B and D at t. The gluing and residue "
                    + "argument gives the original identity K for the signed modes. "),
                Ref(Prefix + "slitChartGerms"), Text(", "), Ref(Identity + "identityK_of_native_chart_germs")))));

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
