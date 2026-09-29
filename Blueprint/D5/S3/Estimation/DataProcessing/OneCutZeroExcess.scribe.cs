using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class OneCutZeroExcessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-cut equality in a twisted cycle.",
        H("One-cut equality in a twisted cycle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("failure-count-equality"),
                DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/OneCutZeroExcess.failure_count_equality_iff_one_cut"),
                H("One-cut equality in a twisted cycle"),
                StatementSource.FromAuthor(Disp(Seq(Call("moving", F.Id("y")), Sp, Le, Sp, Call("failures", F.Id("y")), Comma, Sp, Open, Call("failures", F.Id("y")), Sp, Eq, Sp, Call("moving", F.Id("y")), Sp, Iff, Sp, Call("oneCut", F.Id("y")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take any alphabet with a permutation and a tuple of positive finite length. Count unequal adjacent labels and add the failure of the twisted closing edge. The moving-anchor indicator is one exactly when the first label is not fixed by the permutation.")),
                    Paragraph(Text("The failure count is at least the moving-anchor indicator. Equality holds exactly when there is a cut such that all coordinates up to the cut equal the anchor and every later coordinate equals its inverse image under the permutation.")),
                    Paragraph(Text("With no internal failures all labels agree. With an internal failure and equality of the two counts, that failure is unique and the closing edge succeeds. The two constant segments therefore have the required values. Conversely a one-cut tuple has exactly the forced failure, including the fixed-anchor case."))),
                DescribeRole.Theorem))));
}
