using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class KernelTranscriptInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula observation = F.Id("O");
        Formula transcript = F.Id("R");
        Formula decision = F.Id("D");
        Formula channel = F.Id("K");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula sampleCount = F.Id("n");
        Formula postprocess = F.Id("P");
        Formula decide = F.Id("A");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula sample = Arrow(Call("Fin", sampleCount), observation);
        Formula channelType = Call("Kernel", state, observation);
        Formula postprocessType = Call("Kernel", sample, transcript);
        Formula decisionType = Call("Kernel", transcript, decision);
        Formula lawAtFirst = Apply(channel, first);
        Formula lawAtSecond = Apply(channel, second);
        Formula samplesAtFirst = Call(
            "ProductMeasure", Call("Fin", sampleCount), lawAtFirst);
        Formula samplesAtSecond = Call(
            "ProductMeasure", Call("Fin", sampleCount), lawAtSecond);
        Formula transcriptAtFirst = Call(
            "bind", Call("bind", samplesAtFirst, postprocess), decide);
        Formula transcriptAtSecond = Call(
            "bind", Call("bind", samplesAtSecond, postprocess), decide);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, observation, Comma, Sp, transcript,
            Comma, Sp, decision, Colon, Sp, type, Comma, RowBreak, Grp(),
            Typeclass("MeasurableSpace", state), Comma, Sp,
            Typeclass("MeasurableSpace", observation), Comma, Sp,
            Typeclass("MeasurableSpace", transcript), Comma, Sp,
            Typeclass("MeasurableSpace", decision), Comma, RowBreak, Grp(),
            channel, Colon, Sp, channelType, Comma, Sp,
            Call("Markov", channel), Comma, RowBreak, Grp(),
            first, Comma, Sp, second, Colon, Sp, state, Comma, Sp,
            lawAtFirst, Sp, Eq, Sp, lawAtSecond, Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, sampleCount, InMacro, Sp, naturals, Comma, Sp,
            postprocess, Colon, Sp, postprocessType, Comma, Sp,
            Call("Markov", postprocess), Comma, RowBreak, Grp(),
            decide, Colon, Sp, decisionType, Comma, Sp, Call("Markov", decide),
            Comma, RowBreak, Grp(),
            transcriptAtFirst, Sp, Eq, Sp, transcriptAtSecond, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Equal kernel laws give equal randomized transcript laws.",
            H("Statistical Kernel Transcript Invariance"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("statistical-kernel-transcript-law-invariance"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ProbabilisticClosure/KernelTranscriptInvariance."
                            + "statistical_kernel_transcript_law_invariant"),
                    H("Equal kernel laws generate equal transcript laws"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The hypothesis is equality of the two probability measures returned "
                                + "by the same Markov channel at x and y. For each public sample "
                                + "count n, the input transcript law is the canonical finite product "
                                + "of that channel measure, including the zero-sample product.")),
                        Paragraph(Text(
                            "The public kernels P and A respectively model arbitrary Markov "
                                + "postprocessing and a randomized decision rule. Composing both "
                                + "with the finite product laws constructs the final transcript laws "
                                + "rather than defining a transcript to have the desired equality.")),
                        Paragraph(Text(
                            "Measure equality is preserved first by the finite product constructor "
                                + "and then by both measure-kernel compositions, which yields the "
                                + "displayed equality for every sample count and both processors."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);
}
