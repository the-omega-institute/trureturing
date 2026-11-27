using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeEllipticDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native Lucas cubic is the actual two-division field and block depth is CM contact order.",
        H("The native Lucas elliptic curve and exact CM contact"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-elliptic-two-division"),
                DeclarationHandle.Create(Module + "native_two_division"),
                H("The native cubic is the full two-division field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the group law on actual nonsingular affine points. Their nonzero two-torsion abscissas "
                    + "are exactly the cubic roots, and these abscissas generate the native canonical cyclic field "
                    + "of degree three. The short Weierstrass model has zero ordinate at every such torsion point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-elliptic-cm-reduction"),
                DeclarationHandle.Create(Module + "earlier_prime_good_reduction"),
                H("The whole later elliptic curve reduces to the same CM model"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At any prime greater than three dividing an earlier block, every later curve has good "
                    + "reduction and reduces to the same equation y squared equals x cubed minus nine x. This "
                    + "identifies the entire reduced curve, not only the splitting behavior of its two-division "
                    + "polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-elliptic-cm-depth"),
                DeclarationHandle.Create(Module + "native_elliptic_cm_contact"),
                H("The exact CM contact order recovers the earlier valuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The j-invariant is 1728 plus the square of twenty-four times the native Lucas coordinate. "
                    + "After an earlier prime occurs, the later coordinate has precisely the valuation of the "
                    + "original block, without further increases. Therefore the j-invariant approaches 1728 to "
                    + "exactly twice that depth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-elliptic-wss-contact"),
                DeclarationHandle.Create(Module + "native_wss_iff_cm_contact"),
                H("A square block divisor is equivalent to fourth-order CM contact"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The earlier prime is a square divisor of its block if and only if a later curve has "
                    + "j-invariant equal to 1728 modulo its fourth power. This is an exact reformulation of the "
                    + "local divisibility condition and does not exclude or exhibit such a prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-elliptic-fixed-twist-points"),
                DeclarationHandle.Create(Module + "twist_points"),
                H("Two constant quadratic twists have explicit rational points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The native cubic evaluates to eight and minus eight at the two arguments one away from the "
                    + "Lucas coordinate. The resulting points on the twists by plus and minus two are certified "
                    + "nonsingular. Separate checked slope formulas do not assert the rank of the base curve."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-elliptic-variable-twist-points"),
                DeclarationHandle.Create(Module + "variable_twist_points"),
                H("Two variable twists have three explicit rational points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There are two explicit nonsingular points on the twist by six times the nonzero Lucas "
                    + "coordinate, and one on the twist by minus three times that coordinate. This statement "
                    + "certifies the points on the actual curves but does not certify their infinite order or "
                    + "independence."))),
                DescribeRole.Theorem))));
}
