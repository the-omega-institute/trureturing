using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class AllSetEncodingRecursionUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniqueness of Recursive Set Encoding.",
        H("Uniqueness of Recursive Set Encoding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-set-encoding-recursion-uniqueness"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/AllSetEncodingRecursionUniqueness.enc_unique"),
                H("Uniqueness of the total recursive encoding"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In any universe, every total function on sets satisfying the Zeckendorf "
                    + "encoding recursion equals Enc. On a finite ordinal, the function returns "
                    + "the natural leaf indexed by that ordinal. On every other set, it returns "
                    + "the ordered pair of tag one and the image of its members under the same "
                    + "function. Membership induction gives equality at every set: the natural "
                    + "branch is fixed, and equality on members determines the image in the "
                    + "other branch."))),
                DescribeRole.Theorem))));
}
