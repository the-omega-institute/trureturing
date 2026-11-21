using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeThreeDivisionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native elliptic three-torsion quartic has an explicit cubic subfield and irreducible reduction.",
        H("The native three-torsion quartic and marked cubic subfield"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-three-torsion-coordinates"),
                DeclarationHandle.Create(Module + "three_torsion_abscissa_iff"),
                H("The quartic encodes the actual affine three-torsion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Apply the exact doubling formula on nonsingular points. Over an algebraically closed "
                    + "characteristic zero field, the roots are precisely the abscissas of the nonzero points "
                    + "killed by three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-three-resolvent-pair-values"),
                DeclarationHandle.Create(Module + "resolvent_split_pair_values"),
                H("The cubic resolvent is the polynomial of the three pairings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three pairing values are computed from the actual four roots in any splitting "
                    + "presentation. Vieta coefficients give the resolvent, which simplifies to a translated "
                    + "pure cubic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-three-quartic-mod-five"),
                DeclarationHandle.Create(Module + "native_quartic_mod5_irreducible"),
                H("The actual quartic is irreducible modulo five at every level"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both possible signed mod-five quartics are irreducible. The positive sign uses a short "
                    + "Bezout certificate against the finite-field polynomial containing every irreducible "
                    + "factor of degree at most two. The negative sign follows by changing the sign of the "
                    + "variable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-three-marked-cubic-subfield"),
                DeclarationHandle.Create(Module + "native_quartic_cubic_subfield"),
                H("The projective splitting field contains a marked cubic subfield"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An actual pairing value in the splitting field, shifted by twice the block and divided "
                    + "by minus four, is a cube root of three times the square of the block. The marked element "
                    + "generates a cubic field by the Eisenstein criterion at three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-three-projective-degree"),
                DeclarationHandle.Create(Module + "native_projective_degree_multiple_twelve"),
                H("The actual projective splitting degree is divisible by twelve"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The splitting field contains both the marked cubic subfield and a degree-four quartic "
                    + "root field. Their coprime degrees divide the projective splitting degree. This endpoint "
                    + "does not identify the full Galois image or the independence of a compositum."))),
                DescribeRole.Theorem))));
}
