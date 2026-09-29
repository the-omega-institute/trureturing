using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class DyadicPrefixDelayRangeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Budget/DyadicPrefixDelayRange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dyadic sensor's successful causal controllers have exact prefix completion times, "
            + "and one controller realizes every prescribed nonnegative period-delay table.",
        H("Dyadic Prefix Completion Times"),
        Blocks(
            Paragraph(Text(
                "Fix d>=0, P=2^(d+1), and a known initial high bit b. A prefix t<P/2 "
                    + "has two sources 2t and 2t+1. The earliest midpoint controller "
                    + "finishes either source at E(t)=P-1+P wt(t)-2t, where wt(t) is "
                    + "the number of nonzero binary digits of t. Controllers receive only "
                    + "raw high-bit observations and their own elapsed clock.")),
            Describe.Lean(
                DescribeId.Create("arbitrary-prefix-delay-table"),
                DeclarationHandle.Create(Prefix + "arbitrary_prefix_delay_table"),
                H("One causal controller realizes an entire delay table"),
                StatementSource.FromAuthor(TableStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The midpoint questions before the final query distinguish the prefix t. "
                        + "At that query the controller adds P K(t) to its waiting increment. "
                        + "The added interval leaves the threshold unchanged, and raw-bit "
                        + "transport preserves both the answer and the completion time. "
                        + "Thus the same tree succeeds on every source and realizes every "
                        + "entry of K simultaneously."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arbitrary-protocol-prefix-time"),
                DeclarationHandle.Create(Prefix + "arbitrary_protocol_prefix_time"),
                H("Every successful controller has a nonnegative period correction"),
                StatementSource.FromAuthor(NecessityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Binary capacity forces each query to cut its current interval at the "
                        + "midpoint. The first forward occurrence of that phase is no later "
                        + "than any successful controller's corresponding query. Induction "
                        + "along every source path gives the earliest-time lower bound; the "
                        + "terminal sibling phase then makes the nonnegative difference an "
                        + "integer multiple of P. Both possible last source bits are included."))),
                DescribeRole.Theorem))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula domain, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, domain, Comma, Sp, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, domain, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Implies, Sp, Grp(b));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Conj(Formula a, Formula b) => Seq(Grp(a), Sp, Land, Sp, Grp(b));
    private static Formula Term() => Call("N", F.Id("p"), Seq(D(2), Sp, Times, Sp, F.Id("t"), Sp, Plus, Sp, F.Id("u")));
    private static Formula Expected() => Seq(Call("E", F.Id("t")), Sp, Plus, Sp,
        F.Id("P"), Sp, Times, Sp, Call("K", F.Id("t")));
    private static Formula ValidPair() => Conj(
        Seq(F.Id("t"), Sp, Lt, Sp, Call("pow", D(2), F.Id("d"))),
        Seq(F.Id("u"), Sp, Lt, Sp, D(2)));

    private static Formula TableStatement() => Disp(All("d", N(), All("b", Call("Fin", D(2)),
        All("K", Seq(N(), Sp, To, Sp, N()), Ex("p", Call("Protocol", Seq(F.Id("d"), Sp, Plus, Sp, D(1))),
            Conj(Call("Correct", F.Id("p")),
                All("t", N(), All("u", N(), Imp(ValidPair(), Eqn(Term(), Expected()))))))))));

    private static Formula NecessityStatement() => Disp(All("d", N(), All("b", Call("Fin", D(2)),
        All("p", Call("Protocol", Seq(F.Id("d"), Sp, Plus, Sp, D(1))),
            Imp(Call("Correct", F.Id("p")), All("t", N(), All("u", N(),
                Imp(ValidPair(), Ex("k", N(), Eqn(Term(), Seq(Call("E", F.Id("t")),
                    Sp, Plus, Sp, F.Id("P"), Sp, Times, Sp, F.Id("k"))))))))))));
}
