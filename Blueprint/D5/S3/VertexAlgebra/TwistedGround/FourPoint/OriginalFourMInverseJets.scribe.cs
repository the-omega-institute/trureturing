using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMInverseJetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMInverseJets.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse half-current Taylor coefficients",
        H("Monomial and analytic substitution"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-fourm-inverse-monomial-coefficient"),
                DeclarationHandle.Create(Prefix + "coefficient_rawLocal_pow_div_halfJacobian"),
                H("Inverse transport of a monomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 0 < x < 1, any chart and any puncture, take the physical "
                    + "Taylor coefficient of degree m of the inverse coordinate to the native power n "
                    + "divided by the half-Jacobian evaluated on the chosen inverse branch. It vanishes for "
                    + "n > m. For n ≤ m it is the inverse lifted scale times the inverse scale to power m, "
                    + "times the negative lowering parameter to power m−n and the generalized binomial "
                    + "coefficient with top m+1/2 and bottom m−n."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-inverse-analytic-coefficient"),
                DeclarationHandle.Create(Prefix + "coefficient_comp_rawLocal_div_halfJacobian"),
                H("Finite substitution for an analytic germ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same chart hypotheses, for any complex germ analytic at zero, "
                    + "the physical Taylor coefficient of degree m after inverse substitution and division by "
                    + "the half-Jacobian is a finite sum over native degrees 0 through m. Each summand is the "
                    + "native Taylor coefficient times its inverse monomial factor. The Taylor remainder "
                    + "after degree m is divisible by the physical coordinate to power m+1."))),
                DescribeRole.Theorem))));
}
