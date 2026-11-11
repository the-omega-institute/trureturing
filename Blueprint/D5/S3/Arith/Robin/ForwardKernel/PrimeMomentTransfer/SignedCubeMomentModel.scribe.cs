using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SignedCubeMomentModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Boolean moments realize centered singular series and their cubic and fourth identities.",
        H("Signed Boolean-cube moments"),
        Blocks(
            Describe.Lean(DescribeId.Create("center-finite-image"), DeclarationHandle.Create(Prefix + "centerFinite_image"), H("Centering commutes with injective transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The finite subset centering transform commutes with transporting all subsets along an injective map."))), DescribeRole.Theorem),
            Paragraph(Text(
                "Let the coordinates on finite subsets B be Y(d,B)=s*1[d in B]-1. "
                + "Boolean incidence-algebra Mobius inversion prescribes the uncentered "
                + "moments C(D)/s^|D|. Its inverse-zeta identity gives the required signed "
                + "functional, with no positivity assertion. The commutative-ring centred product expansion applies directly in the algebra of cube functions to identify square-free moments. The resulting formal values "
                + "supply the coefficient identities used in interval moment bounds.")),
            Describe.Lean(
                DescribeId.Create("formal-second-moment-eq"),
                DeclarationHandle.Create(Prefix + "formal_second_moment_eq"),
                H("The formal second value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For normalized empty and singleton data and nonzero s, the second coefficient moment is its ordered distinct-index moment plus (s-1) times the sum of the product of the two coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("formal-third-moment-eq"),
                DeclarationHandle.Create(Prefix + "formal_third_moment_eq"),
                H("The formal cubic value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cubic coefficient moment is the ordered distinct triple sum, plus (s-2) times the three distinct pair sums formed by multiplying two coefficient functions, plus (s-2)(s-1) times the full diagonal coefficient sum. This is quadratic_third_moment_eq applied with a=s-2 and b=s-1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("formal-fourth-pairing-defect"),
                DeclarationHandle.Create(Prefix + "formal_fourth_pairing_defect"),
                H("The formal fourth pairing defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fourth moment minus its three products of second moments equals the distinct fourth pairing defect, plus the six repeated-pair terms with coefficient s-2, the three pair-pair terms with coefficient (s-2)^2, the four triple-singleton terms with coefficient (s-2)^2-2(s-1), and the full diagonal with coefficient (s-2)^2(s-1)-2(s-1)^2. The equality applies quadratic_fourth_pairing_defect without reclassifying index patterns."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phi-eq-formal-moment"),
                DeclarationHandle.Create(Prefix + "Phi_eq_formalMoment"),
                H("Interval values as finite coefficient moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On any finite set containing all interval shifts, Phi equals the general formal coefficient moment with the interval indicator coefficients and singular series transported by the inclusion into the natural numbers. This equality holds for arbitrary s and arbitrary singular-series data."))),
                DescribeRole.Theorem))));
}
