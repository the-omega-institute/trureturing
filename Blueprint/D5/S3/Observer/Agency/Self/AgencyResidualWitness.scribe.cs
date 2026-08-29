using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Self;

internal sealed class AgencyResidualWitnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Agency/Self/AgencyResidualWitness."
            + "hidden_strategy_difference_is_residual";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A hidden strategy difference is a concrete witness of agency residual.",
        H("Agency Residual Witness"),
        Blocks(Describe.Lean(
            DescribeId.Create("agency-residual-witness"),
            DeclarationHandle.Create(Declaration),
            H("Agency Residual Witness"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Two histories may share the same current observer state while encoding different strategy profiles.")),
                Paragraph(Text(
                    "Such a pair lies in the agency residual and is separated by the paired agency completion."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("same_current_and_distinct_strategy"), Sp, Rightarrow, Sp,
            F.Id("agency_residual_witness"), Dot));
}
