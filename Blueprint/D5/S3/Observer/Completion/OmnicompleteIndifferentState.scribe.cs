using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class OmnicompleteIndifferentStateDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Completion/OmnicompleteIndifferentState.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An omnicomplete indifferent state has full support, symmetry invariance, "
            + "prescribed finite projections, and zero completion defect.",
        H("Omnicomplete Indifferent States"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-conditions-for-an-omnicomplete-indifferent-state"),
                DeclarationHandle.Create(DeclarationPrefix + "OmnicompleteSystem"),
                H("Four conditions for an omnicomplete indifferent state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The structure carries a measure whose support is the whole state "
                            + "space, whose pushforward by every symmetry is itself, whose "
                            + "pushforward along every finite projection is the prescribed "
                            + "finite measure, and whose completion defect vanishes at every "
                            + "finite level.")),
                    Paragraph(Text(
                        "The conditions are jointly realizable. On the two-point Boolean state "
                            + "space, counting measure has full support and gives each singleton "
                            + "mass one; the one-element group acts trivially, every finite "
                            + "projection is the identity, and every defect is zero. The Lean "
                            + "theorem exists_bool_omnicomplete_indifferent_state constructs "
                            + "this nontrivial instance."))),
                DescribeRole.Definition))));
}
