using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicThueEisensteinDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A primary square-role norm gives one monic integral cubic with two Eisenstein certificates.",
        H("Eisenstein tests for the monic Thue companion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-shifted-coefficients"),
                DeclarationHandle.Create(Module + "shifted_eq_comp"),
                H("Exact coefficients after translating the variable by one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Substituting X+1 in the companion cubic gives quadratic coefficient "
                    + "3-6P, linear coefficient 3-12P+9P^2, and constant "
                    + "1-6P+9P^2-E^2P."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-primary-pair-eisenstein"),
                DeclarationHandle.Create(Module + "primary_pair_eisenstein"),
                H("The same companion is Eisenstein at the role prime and after shifting at three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a and b be the primary integral coordinates, a congruent to one "
                        + "and b to zero modulo three, with prime norm P = a^2-ab+b^2. "
                        + "Put A = a^2-b^2, D = 2ab-b^2 and E = A-2D. The monic companion "
                        + "is X^3-6PX^2+9P^2X-E^2P. The norm identity and primality rule "
                        + "out P dividing E, so the companion is Eisenstein at P.")),
                    Paragraph(Text(
                        "The substitution X+1 makes the constant congruent to three modulo "
                        + "nine. The two other nonleading coefficients are divisible by "
                        + "three, so the shifted companion is Eisenstein at three. "
                        + "The theorem is a polynomial statement, not an assertion about "
                        + "the maximal order, field discriminant, or conductor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-native-role-eisenstein"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.native_role_pair_eisenstein"),
                H("Both local certificates attach to the actual native square role"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the proposed two-prime Lucas block, the same generator of the "
                    + "original square ideal gives a monic degree-three polynomial that is "
                    + "Eisenstein at the role prime and, after translation, at three."))),
                DescribeRole.Theorem))));
}
