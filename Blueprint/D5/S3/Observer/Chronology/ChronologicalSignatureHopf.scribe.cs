using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class ChronologicalSignatureHopfDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/ChronologicalSignatureHopf.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Step-two chronological signatures satisfy the group-like coproduct and "
            + "antipode laws, and the antipode reverses event order with negated "
            + "values.",
        H("Chronological Signature Group-Like Hopf Laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coproduct"),
                DeclarationHandle.Create(Prefix + "groupLikeCoproduct"),
                H("Group-like diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite group-like coproduct sends a signature to two identical copies."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coproduct-mul"),
                DeclarationHandle.Create(Prefix + "group_like_coproduct_mul"),
                H("Multiplicative diagonal"),
                StatementSource.FromAuthor(CoproductMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The diagonal preserves chronological multiplication componentwise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coassociative"),
                DeclarationHandle.Create(Prefix + "group_like_coproduct_coassociative"),
                H("Coassociative group-like diagonal"),
                StatementSource.FromAuthor(CoassociativityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Either order of iterating the diagonal produces three identical signature components."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("left-convolution"),
                DeclarationHandle.Create(Prefix + "antipode_left_convolution"),
                H("Left antipode cancellation"),
                StatementSource.FromAuthor(LeftConvolutionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplying the antipode leg by the identity leg yields the empty signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-convolution"),
                DeclarationHandle.Create(Prefix + "antipode_right_convolution"),
                H("Right antipode cancellation"),
                StatementSource.FromAuthor(RightConvolutionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplying the identity leg by the antipode leg yields the empty signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-negate"),
                DeclarationHandle.Create(Prefix + "chronological_signature_reverse_neg"),
                H("Reverse-and-negate realizes the antipode"),
                StatementSource.FromAuthor(ReverseNegFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reversing an event word and negating every observed value gives exactly the antipode of its chronological signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-reverse-negate"),
                DeclarationHandle.Create(Prefix + "chronological_log_reverse_neg"),
                H("Reverse-and-negate in logarithmic coordinates"),
                StatementSource.FromAuthor(LogReverseNegFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After applying the logarithm, reverse-and-negate becomes coordinatewise negation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-involutive"),
                DeclarationHandle.Create(Prefix + "chronological_signature_reverse_neg_involutive"),
                H("Involutive chronology reversal"),
                StatementSource.FromAuthor(ReverseNegInvolutiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying the finite antipode after reverse-and-negate recovers the original signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-append"),
                DeclarationHandle.Create(Prefix + "chronological_signature_reverse_neg_append"),
                H("Reversal of concatenation"),
                StatementSource.FromAuthor(ReverseNegAppendFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reverse-and-negate sends concatenation to the reversed product of the two antipodes."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Cop(Formula value) =>
        Call("groupLikeCoproduct", value);

    private static Formula FstOf(Formula value) => Call("fst", value);

    private static Formula SndOf(Formula value) => Call("snd", value);

    private static Formula AntipodeOf(Formula value) =>
        Call("signatureAntipode", value);

    private static Formula SigNegRev(Formula word) =>
        Call("chronologicalSignature",
            Seq(F.Id("x"), Sp, Mapsto, Sp, Minus,
                Call("f", F.Id("x"))),
            Call("reverse", word));

    private static Formula SigOf(Formula word) =>
        Call("chronologicalSignature", F.Id("f"), word);

    private static Formula Triple(Formula a, Formula b, Formula c) =>
        Seq(Open, a, Comma, Sp, b, Comma, Sp, c, Close);

    private static Formula CoproductMulFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
        Cop(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("b"))), Sp, Eq, Sp,
        Open,
        FstOf(Cop(F.Id("a"))), Sp, Cdot, Sp, FstOf(Cop(F.Id("b"))),
        Comma, Sp,
        SndOf(Cop(F.Id("a"))), Sp, Cdot, Sp, SndOf(Cop(F.Id("b"))),
        Close, Dot));

    private static Formula CoassociativityFormula()
    {
        Formula a = F.Id("a");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, a, Colon,
            RowBreak, Grp(),
            Triple(FstOf(Cop(a)),
                FstOf(Cop(SndOf(Cop(a)))),
                SndOf(Cop(SndOf(Cop(a))))),
            RowBreak, Grp(),
            Eq, Sp,
            Triple(FstOf(Cop(FstOf(Cop(a)))),
                SndOf(Cop(FstOf(Cop(a)))),
                SndOf(Cop(a))), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula LeftConvolutionFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp,
        AntipodeOf(FstOf(Cop(F.Id("a")))), Sp, Cdot, Sp,
        SndOf(Cop(F.Id("a"))), Sp, Eq, Sp, D(1), Dot));

    private static Formula RightConvolutionFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp,
        FstOf(Cop(F.Id("a"))), Sp, Cdot, Sp,
        AntipodeOf(SndOf(Cop(F.Id("a")))), Sp, Eq, Sp, D(1), Dot));

    private static Formula ReverseNegFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("L"), Comma, Sp,
        SigNegRev(F.Id("L")), Sp, Eq, Sp,
        AntipodeOf(SigOf(F.Id("L"))), Dot));

    private static Formula LogReverseNegFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("L"), Comma, Sp,
        Call("chronologicalLog", SigNegRev(F.Id("L"))), Sp, Eq, Sp,
        Call("inverse", Call("chronologicalLog", SigOf(F.Id("L")))), Dot));

    private static Formula ReverseNegInvolutiveFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("L"), Comma, Sp,
        AntipodeOf(SigNegRev(F.Id("L"))), Sp, Eq, Sp,
        SigOf(F.Id("L")), Dot));

    private static Formula ReverseNegAppendFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("P"), Comma, Sp, F.Id("S"),
        Colon,
        RowBreak, Grp(),
        SigNegRev(Call("append", F.Id("P"), F.Id("S"))),
        RowBreak, Grp(),
        Eq, Sp,
        AntipodeOf(SigOf(F.Id("S"))), Sp, Cdot, Sp,
        AntipodeOf(SigOf(F.Id("P"))), Dot,
        End, Grp(F.Id("gathered"))));
}
