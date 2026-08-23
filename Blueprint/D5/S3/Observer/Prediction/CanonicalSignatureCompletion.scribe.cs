using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Prediction;

internal sealed class CanonicalSignatureCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical signatures recover finite words, the canonical stable depth, and completion.",
        H("Canonical Signature Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-signature-labels-stable-depth-and-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Prediction/CanonicalSignatureCompletion."
                        + "canonical_signature_labels_stable_depth_and_completion"),
                H("Canonical signatures equal finite future classes"),
                StatementSource.FromAuthor(SignatureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y and O be finite, let tau be a deterministic update, and let q be "
                            + "a surjective readout. The canonical controlled-signature algorithm "
                            + "is specialized to the singleton input carrier, so its input words "
                            + "are exactly finite iterates of tau.")),
                    Paragraph(Text(
                        "The imported controlled-signature correctness theorem then identifies "
                            + "signature equality with the finite-future relation at every depth. "
                            + "The imported observation refinement theorem supplies the existing "
                            + "least adjacent-partition stability depth directly.")),
                    Paragraph(Text(
                        "At that canonical depth, the first-isomorphism equivalence for the "
                            + "controlled-signature map is followed by the existing stable "
                            + "finite-to-complete quotient equivalence. The resulting named map "
                            + "sends every realized signature to the complete class of its state."))),
                DescribeRole.Theorem))));

    private static Formula SignatureFormula()
    {
        Formula stateType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula update = Tau;
        Formula readout = F.Id("q");
        Formula depth = F.Id("m");
        Formula first = F.Id("y");
        Formula second = Seq(F.Id("y"), Apos);
        Formula signature = F.Id("controlledSignature");
        Formula signatureAt = Seq(signature, Underscore, Grp(depth));
        Formula nextSignature = Seq(
            signature, Underscore, Grp(Seq(depth, Plus, D(1))));
        Formula firstLabel = Seq(signatureAt, Open, first, Close);
        Formula secondLabel = Seq(signatureAt, Open, second, Close);
        Formula finiteRelation = Seq(
            Equiv, Underscore, Grp(depth), Caret, Grp(readout));
        Formula stableDepth = new Formula.Subscript(F.Id("m"), Star);
        Formula stableSignature = Seq(signature, Underscore, Grp(stableDepth));
        Formula nextStableSignature = Seq(
            signature, Underscore, Grp(Seq(stableDepth, Plus, D(1))));
        Formula kernel = F.Id("ker");
        Formula completion = new Formula.Subscript(F.Id("Z"), readout);
        Formula realized = Seq(
            Operatorname, Grp(F.Id("range")), Open, stableSignature, Close);
        Formula canonical = F.Id("E");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, outputType, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, stateType, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, outputType, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Open, stateType, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            update, Colon, Sp, stateType, Sp, To, Sp, stateType, Comma, Sp,
            readout, Colon, Sp, stateType, Sp, To, Sp, outputType, Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("Surjective")), Open, readout, Close, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, depth, Comma, Sp, first, Comma, Sp, second, Comma, Sp,
            firstLabel, Sp, Eq, Sp, secondLabel, Sp, Iff, Sp,
            first, Sp, finiteRelation, Sp, second, Close, Sp, Land,
            RowBreak, Grp(),
            kernel, Open, Seq(signature, Underscore, Grp(stableDepth)), Close,
            Sp, Eq, Sp,
            kernel, Open, nextStableSignature, Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, depth, Comma, Sp,
            kernel, Open, signatureAt, Close, Sp, Eq, Sp,
            kernel, Open, nextSignature, Close, Sp, Rightarrow, Sp,
            stableDepth, Sp, Leq, Sp, depth, Close, Sp, Land, RowBreak, Grp(),
            canonical, Colon, Sp, realized, Sp, Equiv, Sp, completion, Comma, Sp,
            Forall, Sp, first, InMacro, Sp, stateType, Comma, Sp,
            canonical, Open, stableSignature, Open, first, Close, Close,
            Sp, Eq, Sp, OpenBracket, first, CloseBracket,
            Underscore, Grp(completion), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
