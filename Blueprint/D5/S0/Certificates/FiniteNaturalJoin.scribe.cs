using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteNaturalJoinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteNaturalJoin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite natural joins preserve the same compatible total event.",
        H("Checked support conflicts retain the original event semantics"),
        Blocks(
            Paragraph(Text("Rows assign arbitrary finite lists of coordinates and values. Duplicate coordinates are permitted: compatibility requires every listed entry to agree with the same total event. No coordinate is fixed or discarded. The computed natural join checks equality on every overlapping coordinate and concatenates exactly the agreeing pairs.")),
            Describe.Lean(DescribeId.Create("join-covers"),
                DeclarationHandle.Create(Prefix + "join_covers"),
                H("Every shared total event survives a natural join"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two compatible witness rows agree on each common coordinate because both use the same actual event. That pair survives the filter, its concatenation occurs in the joined relation, and all its entries retain compatibility. Repeated application therefore lets an actual computed empty join exclude simultaneous support membership. The original EJM support-conflict consumer supplies the full finite inputs and checks the empty join with the Lean kernel."))),
                DescribeRole.Theorem))));
}
