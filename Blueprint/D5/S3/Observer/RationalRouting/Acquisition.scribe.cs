using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.RationalRouting;

internal sealed class AcquisitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite dyadic acquisition recovers every original rational with acquired cap two or preset cap four.",
        H("Acquiring the original on the same source"),
        Blocks(
            Describe.Lean(DescribeId.Create("rational-source-run-uniqueness"),
                DeclarationHandle.Create("D5/S3/Observer/RationalRouting/Acquisition.run_unique"),
                H("Deterministic terminal runs agree"),
                StatementSource.FromAuthor(Uniqueness()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two finite runs of the same deterministic code, original source, initial state and starting chronological prefix have identical whole outputs, final words and read histories. Induction through each actual instruction compares the unique report continuation. The output type is arbitrary. This also applies when the final local calculation constructs a different exact original view."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("actual-rational-acquisition"),
                DeclarationHandle.Create("D5/S3/Observer/RationalRouting/Acquisition.actual_rational_acquisition"),
                H("Pointwise finite full-rational acquisition"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The explicit source-independent instruction function has two modes. Both actually read q_2 at the original cut. In acquired mode this report selects LL on the first band and RL on the second. Preset mode follows LLRL throughout, stopping motion after LL on the first band and after its fourth letter on the second. No letters are skipped or restarted. The state contains only a phase, acquired band and public remaining word, or candidate and scale counters, or a recovered rational ready for output.")),
                    Paragraph(Text("At the attained cut the endpoint reports are respectively floor(8z)=1, floor(8z)=5 and floor(16z)=9. Strict increase makes equality with that integer equivalent to the original being its band's included endpoint. This finite read resolves each accumulation endpoint without waiting for a nondyadic equality.")),
                    Paragraph(Text("Otherwise, for each candidate j starting at 12, form the public midpoint between f_u(c_i-1/j) and f_u(c_i-1/(j+1)). Repeated actual reads at the same attained cut refine a dyadic cell. Stop the comparison when its upper endpoint is at most the midpoint or its lower endpoint is strictly larger. Every promised transformed tail point differs from this midpoint; a sufficiently small cell therefore stops. For actual index n, comparisons are above until j=n and below at n. The nested loops are finite on each member, with no uniform bound on n, scales, read count, arithmetic or output length.")),
                    Paragraph(Text("The conjunction asserts finite correct whole-rational output for both modes, acquired cap 2, preset cap 4, compliance with the one LLRL schedule, and positivity of every prior member. Run uniqueness supplies correctness and action counts for every completed run. The source is never reset, copied, inverted or queried through an exact unknown rational argument."))),
                DescribeRole.Theorem))));

    private static Formula Uniqueness() => Disp(Seq(
        Call("Run", F.Id("C"), F.Id("x"), F.Id("s"), F.Id("w"), F.Id("o"), F.Id("v"), F.Id("A")), Land, Sp,
        Call("Run", F.Id("C"), F.Id("x"), F.Id("s"), F.Id("w"), F.Id("o1"), F.Id("v1"), F.Id("A1")),
        Longrightarrow, Sp, F.Id("o"), Eq, F.Id("o1"), Land, Sp,
        F.Id("v"), Eq, F.Id("v1"), Land, Sp, F.Id("A"), Eq, F.Id("A1")));
    private static Formula Statement() => Disp(Seq(
        Call("Correct", F.Id("Crec"), F.Id("id")), Land, Call("Cap", F.Id("Crec"), D(2)), Land, Sp,
        Call("Correct", F.Id("Cpre"), F.Id("id")), Land, Call("Cap", F.Id("Cpre"), D(4)), Land, Sp,
        Call("Preset", F.Id("Cpre"), F.Id("LLRL")), Land, Sp,
        Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("P"), Comma, Sp, D(0), Lt, F.Id("x")));
}
