using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Endpoints;

internal sealed class XiEndpointValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pole-removed completed-zeta xi reading has value one-half at both endpoints.",
        H("Xi Endpoint Values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("xi-reading-endpoint-values-equal-one-half"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Endpoints/XiEndpointValues.xi_reading_endpoint_values"),
                H("Xi reading endpoint values equal one-half"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("xiReading")), Open, D(0), Close, Eq,
                    Frac, Grp(D(1)), Grp(D(2)), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("xiReading")), Open, D(1), Close, Eq,
                    Frac, Grp(D(1)), Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The endpoint values are definitionally immediate from the frozen pole-removed "
                        + "xi reading: at zero and one, the factor s times s minus one vanishes, leaving "
                        + "one half.")),
                    Paragraph(Text(
                        "This module records those values as an addressable certificate discharging the "
                        + "ledger claim. It asserts no additional pole or continuation clause."))),
                DescribeRole.Theorem)),
        []));
}
