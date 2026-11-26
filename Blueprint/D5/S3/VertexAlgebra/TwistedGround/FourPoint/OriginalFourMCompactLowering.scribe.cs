using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMCompactLoweringDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native occupations of four inverse lowerings",
        H("Fixed-charge coefficients"),
        Blocks(
            Result("four-m-physical-marked-compact-lowering", "physical_marked_compact_lowering",
                "Physical coefficient of four lowering words",
                "For a unit Gram determinant and a word of distinct marked occurrences, "
                + "use A or B in its radial disk or the true D lip at a real chart argument "
                + "strictly between zero and one. The fixed-charge marked coefficient is the "
                + "charge exponential times the product of the signed lifted scales and the "
                + "compact affine readout of the four tagged puncture lowering words. "
                + "Reflect the finite creator sum to match the inverse jet rows and recombine "
                + "each puncture's corrections with the surviving creators."),
            Result("four-m-affine-coefficient-occupied-support", "affineCoefficient_fourSupport",
                "Affine coefficient on the occupied support",
                "For each chart and four occupations, the affine coefficient in any common "
                + "finite support containing the four occupied supports equals the coefficient "
                + "on their union. Embed the exponent independently in each tagged slot. "
                + "The extended exponent has the same covariance and charge-linear mean "
                + "on the occupied slots, including at the true D lip."),
            Result("four-m-compact-readout-native", "compact_readout_eq_native",
                "Native readout of four oscillator polynomials",
                "Suppose the four oscillator polynomials have all their variables in a common "
                + "finite support. Multiply their tagged images in native slot order and "
                + "evaluate the compact affine readout with the chart determinant and charge "
                + "nome power. The result is the sum over the four polynomials' occupied "
                + "monomials of the products of their coefficients and factorial Fock "
                + "weights times the literal native fixed-charge term at each occupation."),
            Result("four-m-lowered-native-occupation-readout", "lowered_charge_eq_native_occupations",
                "Native coefficient of the actual inverse lowerings",
                "Take a real chart argument strictly between zero and one and the upper "
                + "choice in chart D. For a charge of nonnegative energy and a finite support "
                + "containing the variables of all four finite inverse lowerings, the "
                + "normalized lowerings give their literal native occupation sum multiplied "
                + "by the signed lifted scales and the cube of one minus the chart parameter."),
            Result("four-m-lowered-support-independent", "loweredChargeTerm_support_independent",
                "Independence of the ambient lowering support",
                "For any chart, argument and charge, take two finite sets containing "
                + "the variables of all four actual inverse lowerings. They give the same normalized "
                + "fixed-charge coefficient. The two evaluations agree term by term with "
                + "the readout on the four individual occupations."))));

    private static DocumentBlock Result(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
