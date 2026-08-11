using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class CascadeContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A relation extendable at every state admits a path through every finite stage.",
        H("Cascade Continuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("locally-extendable-relations-admit-coherent-infinite-paths"),
                DeclarationHandle.Create("D5/S0/Rewriting/CascadeContinuation.cascade_continues_to_all_stages"),
                H("Every stage has a coherent successor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("s"), Comma, Sp,
                    Exists, Sp, F.Id("t"), Comma, Sp,
                    F.Id("step"), Open, F.Id("s"), Comma, Sp, F.Id("t"), Close,
                    Close, Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("path"), Comma, Sp,
                    F.Id("path"), Open, D(0), Close, Sp, Eq, Sp, F.Id("start"),
                    Sp, Land, Sp,
                    Forall, Sp, F.Id("n"), Comma, Sp,
                    F.Id("step"), Open,
                    F.Id("path"), Open, F.Id("n"), Close, Comma, Sp,
                    F.Id("path"), Open, F.Id("n"), Plus, D(1), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source atom supplies a successor at every state. Choosing one "
                        + "such successor uniformly and iterating that choice produces a single "
                        + "stage-indexed path whose adjacent states satisfy the relation.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the iteration identities used to verify the "
                        + "initial and successor stages, but it has no declaration that builds "
                        + "this path from the local existence premise. The proof is therefore a "
                        + "new assembly of choice and iteration rather than a wrapper."))),
                DescribeRole.Theorem))));
}
