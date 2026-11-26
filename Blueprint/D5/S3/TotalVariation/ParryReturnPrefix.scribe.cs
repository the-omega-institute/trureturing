using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryReturnPrefixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite relation prefixes under independent return-duration weights.",
        H("Raw windows under arbitrary return-duration weights"),
        Blocks(Describe.Lean(
            DescribeId.Create("iid-return-raw-prefix"),
            DeclarationHandle.Create("D5/S3/TotalVariation/ParryReturnPrefix.iid_return_prefix"),
            H("A raw prefix carries a duration tail factor"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take any measure on native admissible relation paths whose complete "
                    + "return-duration cylinder masses factor with common weights on Fin k. "
                    + "A raw window specifying a finite list of complete returns and then "
                    + "j consecutive true bits has mass equal to the completed-return "
                    + "product times the tail mass of durations strictly greater than j.")),
                Paragraph(Text(
                    "After the specified returns, the next j bits are true exactly when "
                    + "the next return takes more than j steps. Partition the event by that "
                    + "next duration. The resulting cylinders are measurable and disjoint. "
                    + "Finite additivity and the assumed cylinder products give the formula."))),
            DescribeRole.Theorem))));
}
