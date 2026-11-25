using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourPointIdentityKDocument : IScribeDocumentDefinition
{
    private const string FourPoint = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/";
    private const string Prefix = FourPoint + "OriginalFourPointIdentityK.";
    private const string Coefficients = FourPoint + "FourPointChannelCoefficients.";
    private const string Residue = "D5/S3/AnalyticClosure/ThreePunctureResidue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original signed-mode identity from common four-point germs",
        H("The residue proof of the charge-coset identity"),
        Blocks(
            D("four-point-actual-iterate-germ", "actualChannelA", "Actual A germ in the residue coordinate",
                DescribeRole.Definition,
                Text("Take the Laurent diagonals of the actual sewn numerators. Sum over input "
                    + "charge classes a with the quadratic sign of a and the Fourier sign for a "
                    + "and the output class b.")),
            D("four-point-actual-direct-germ", "actualChannelB", "Actual B germ before the prefactor",
                DescribeRole.Definition,
                Text("In the output class b, use the reflected Laurent diagonal on Q, R, P "
                    + "and the finitely lowered detector S, with the original lowering weights. "
                    + "The chart multiplies this germ by 2¹² z^(m+n+r+2).")),
            D("four-point-actual-inverse-germ", "actualChannelD", "Actual D germ in the inverse coordinate",
                DescribeRole.Definition,
                Text("Use the reflected Laurent diagonals on P, R, Q and the finitely lowered "
                    + "detector S. Sum over classes a with the quadratic sign of a + b.")),
            T("four-point-identity-k-common-germ", "identityK_of_common_four_point_germ",
                "The signed-mode identity from three Laurent expansions",
                Text("Assume the Gram matrix is positive definite with unit determinant and the "
                    + "three analytic numerator families have the Taylor coefficients of the "
                    + "original diagonal coset kernels. For each output class b, let F be "
                    + "holomorphic on ℂ ∖ {0, 1}. Assume its punctured germs are the A combination "
                    + "at (1 − z)/z near one, 2¹² z^(m+n+r+2) times the B combination at z near "
                    + "zero, and the D combination at u near u = 0 in the coordinate z = u⁻¹. "
                    + "Apply residue balance to "
                    + "(1 − z)^r z^(−m−r−2) F(z) dz. At zero the B prefactor leaves "
                    + "2¹² z^n (1 − z)^r times the B germ. At one the iterate Jacobian "
                    + "produces the negative signed A residue in the variable t = (1 − z)/z. "
                    + "Inversion gives the negative signed D residue, with weight u^m (u − 1)^r. "
                    + "The sum of these three simple coefficients is exactly the original charge-coset "
                    + "identity for the signed modes m, n, r. "),
                Ref(Coefficients + "hasPrincipalPart_channelA"), Text(", "),
                Ref(Coefficients + "hasPrincipalPart_channelB"), Text(", "),
                Ref(Coefficients + "hasPrincipalPart_channelD"), Text(", "),
                Ref(Residue + "aChart_residue_invariant"), Text(", "),
                Ref(Residue + "residue_sum_of_differential_expansions")),
            T("four-point-identity-k-actual-germs", "identityK_of_common_actual_channel_germs",
                "Specializing to the actual sewn numerators",
                Text("With a positive definite Gram matrix of unit determinant, the sewn "
                    + "diagonal specification supplies the numerator hypotheses for "
                    + "all three channels, including every term below the B and D lowering "
                    + "cutoff. For each output class, assume a common function holomorphic on "
                    + "ℂ ∖ {0, 1} with punctured germs given by actual A at (1 − z)/z near one, "
                    + "2¹² z^(m+n+r+2) times actual B at z near zero, and actual D at u near "
                    + "u = 0 for z = u⁻¹. These hypotheses give the original identity. "),
                Ref(Coefficients + "actualDiagonalNumerator_spec"), Text(", "),
                Ref(Prefix + "identityK_of_common_four_point_germ")),
            T("four-point-identity-k-native-charts", "identityK_of_native_chart_germs",
                "From native chart germs and overlap equalities to the identity",
                Text("Assume the Gram matrix is positive definite with unit determinant. For "
                    + "each output class, take A, B and D holomorphic on the punctured Euler slit. "
                    + "At native zero their punctured germs agree with actual A at −t and actual "
                    + "B and D at t, respectively. Assume A(1 − z⁻¹) = 2¹² z^(m+n+r+2) B(z) "
                    + "accumulates at an interior point of the double slit. Assume either "
                    + "A(1 − z⁻¹) = D(z⁻¹) accumulates at a point of U_A ∩ U_D, or "
                    + "2¹² z^(m+n+r+2) B(z) = D(z⁻¹) accumulates at a point of U_B ∩ U_D. "
                    + "Gluing supplies the common function used in the residue proof. "),
                Ref(FourPoint + "OriginalFourPointChartGluing.exists_common_four_point_germ"), Text(", "),
                Ref(Prefix + "identityK_of_common_actual_channel_germs")))));

    private static DocumentBlock T(string id, string declaration, string title, params Inline[] content) =>
        D(id, declaration, title, DescribeRole.Theorem, content);

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
