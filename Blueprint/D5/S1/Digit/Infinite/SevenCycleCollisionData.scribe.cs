using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleCollisionDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven-phase source coordinates.",
        H("Seven-phase source coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sevencyclecollisiondata-budget"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/SevenCycleCollisionData.budget"),
                H("Subcritical observation radius"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The radius is lambda minus g^7*(g-1/5)/(4*(1+g^7)), where g is the "
                    + "original three-bit contraction. The source streams repeat the windows "
                    + "3,3,5,5,3,2,2 and 0,3,5,5,3,2,2. Their guards are 0,0,0,1,1,0,0. "
                    + "The scalar phase function uses the original branch maps for the common "
                    + "six-window suffix."))), DescribeRole.Definition))));
}
