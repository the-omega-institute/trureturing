using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class AllSetNaturalLeafMembersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Members of Natural Leaves.",
        H("Members of Natural Leaves"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-set-natural-leaf-members"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/AllSetNaturalLeafMembers.el_natZ"),
                H("Smaller natural leaves"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In any universe, the encoding of the finite von Neumann ordinal of a natural "
                    + "number is its natural leaf. Its semantic members are exactly the natural leaves "
                    + "of all strictly smaller natural numbers. The set of members is the range of "
                    + "the natural leaf map on those smaller indices, including the empty range at zero."))),
                DescribeRole.Theorem))));
}
