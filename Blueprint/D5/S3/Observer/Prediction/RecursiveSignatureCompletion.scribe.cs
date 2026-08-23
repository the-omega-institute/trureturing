using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Prediction;

internal sealed class RecursiveSignatureCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive signatures recover finite-future classes and their stable completion.",
        H("Recursive Signature Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("recursive-signature-labels-stable-depth-and-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Prediction/RecursiveSignatureCompletion."
                        + "recursive_signature_labels_stable_depth_and_completion"),
                H("Signature labels equal finite future classes"),
                StatementSource.FromAuthor(SignatureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y and O be finite, let the deterministic update be tau, and let q "
                            + "map Y surjectively onto the actual readout carrier O. The "
                            + "depth-zero "
                            + "label is q itself. Each later label is the pair consisting of the "
                            + "current readout and the preceding label after one update.")),
                    Paragraph(Text(
                        "Induction identifies equality of these recursively constructed labels "
                            + "with equality of every readout through the same finite horizon. "
                            + "Consequently the first adjacent pair of label partitions that "
                            + "agree occurs at exactly the canonical finite-observation stability "
                            + "depth.")),
                    Paragraph(Text(
                        "At that depth, the first-isomorphism equivalence sends realized labels to "
                            + "the finite prediction quotient. The existing stable quotient "
                            + "equivalence then gives the named canonical map to complete-future "
                            + "state classes, and its representative equation sends the label of y "
                            + "to the complete quotient class of y."))),
                DescribeRole.Theorem))));

    private static Formula SignatureFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = Tau;
        Formula readout = F.Id("q");
        Formula depth = F.Id("m");
        Formula first = F.Id("y");
        Formula second = Seq(F.Id("y"), Apos);
        Formula label = F.Id("c");
        Formula labelAt = Seq(label, Underscore, Grp(depth));
        Formula firstLabel = Seq(labelAt, Open, first, Close);
        Formula secondLabel = Seq(labelAt, Open, second, Close);
        Formula finiteRelation = Seq(
            Equiv, Underscore, Grp(depth), Caret, Grp(readout));
        Formula stableDepth = new Formula.Subscript(F.Id("m"), Star);
        Formula nextLabel = Seq(
            label, Underscore, Grp(Seq(depth, Plus, D(1))));
        Formula finalLabels = Seq(
            label, Underscore, Grp(stableDepth), Open, state, Close);
        Formula completeRelation = Seq(
            Equiv, Underscore, Grp(Infty), Caret, Grp(readout));
        Formula completion = Seq(state, Slash, completeRelation);
        Formula canonical = F.Id("E");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, state, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, output, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            Operatorname, Grp(F.Id("Surjective")), Open, readout, Close, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, depth, Sp, Geq, Sp, D(0), Comma, Sp,
            first, Comma, Sp, second, InMacro, Sp, state, Comma, Sp,
            firstLabel, Sp, Eq, Sp, secondLabel, Sp, Iff, Sp,
            first, Sp, finiteRelation, Sp, second, Close, Sp, Land, RowBreak, Grp(),
            Min, OpenBrace, depth, Sp, Mid, Sp,
            nextLabel, Sp, Sim, Sp, labelAt, CloseBrace,
            Sp, Eq, Sp, stableDepth, Sp, Land, RowBreak, Grp(),
            canonical, Colon, Sp, finalLabels, Sp, Equiv, Sp, completion, Comma, Sp,
            Forall, Sp, first, InMacro, Sp, state, Comma, Sp,
            canonical, Open,
            Seq(label, Underscore, Grp(stableDepth)), Open, first, Close,
            Close, Sp, Eq, Sp, OpenBracket, first, CloseBracket,
            Underscore, Grp(completeRelation), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
