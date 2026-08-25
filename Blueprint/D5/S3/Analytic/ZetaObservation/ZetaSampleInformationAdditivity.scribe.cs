using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class ZetaSampleInformationAdditivityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent zeta observations add their Fisher information exactly.",
        H("Zeta Sample Information Additivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeta-sample-information-additivity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/ZetaObservation/"
                        + "ZetaSampleInformationAdditivity."
                        + "zeta_sample_information_additive"),
                H("Independent zeta samples have additive information"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The one-sample Fisher information is represented by the variance "
                            + "of the logarithmic observation under the zeta law. The m-sample "
                            + "quantity is the variance of the sum of the m coordinate "
                            + "observations under the canonical product zeta measure.")),
                    Paragraph(Text(
                        "Above inverse temperature one, the logarithmic observation has a "
                            + "finite second moment. Variance additivity for the independent "
                            + "product coordinates then makes the joint information exactly m "
                            + "times the one-sample information, including the zero-sample "
                            + "case."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula exponent = F.Id("s");
        Formula sampleCount = F.Id("m");
        Formula domain = new Formula.Relation(
            F.D(1), FormulaRelationOperator.LessThan, exponent);
        Formula jointInformation = Call(
            "VarianceUnder",
            Call("ProductZetaLaw", exponent, sampleCount),
            Call("SumOfLogCoordinates", sampleCount));
        Formula singleInformation = Call(
            "VarianceUnder",
            Call("ZetaLaw", exponent),
            Call("LogObservation"));
        Formula conclusion = new Formula.Relation(
            jointInformation,
            FormulaRelationOperator.Equal,
            Call("Product", sampleCount, singleInformation));

        return F.Disp(F.Seq(
            F.Forall, F.Sp, exponent, F.Colon, F.Sp, F.Mathbb, F.Grp(F.Id("R")),
            F.Comma, F.Sp, sampleCount, F.Colon, F.Sp, F.Mathbb, F.Grp(F.Id("N")),
            F.Comma, F.Esc,
            new Formula.Logic(
                domain,
                FormulaLogicOperator.Implies,
                conclusion)));
    }
}
