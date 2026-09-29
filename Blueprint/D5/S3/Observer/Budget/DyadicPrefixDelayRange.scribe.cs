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
                DescribeId.Create("delayed-midpoint-execute"),
                DeclarationHandle.Create(Prefix + "delayed_midpoint_execute"),
                H("Delay-table execution on both final-bit siblings"),
                StatementSource.FromAuthor(DelayedStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any P, delay table K, and readout agreeing with the threshold below P "
                        + "and invariant under addition of P periods, the recursively delayed "
                        + "midpoint tree returns the same answer as the earliest tree. Its actual "
                        + "last-read time adds exactly P K(floor(r/2)). The source interval has "
                        + "even start a, length 2^(d+1), and lies below P; r ranges over that "
                        + "whole interval, with arbitrary initial time now."))),
                DescribeRole.Theorem),
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
                DescribeRole.Theorem),
            Paragraph(Text(
                "For deadline D, F_D is the family of actual successful depth-(d+1) "
                    + "raw-bit protocols whose last read is at most D on every source r<P. "
                    + "Write W=sharpWait(d+1), E(t)=P-1+P wt(t)-2t, N_p(r) for the actual "
                    + "last-read time, and Y_p(r) for the raw final bit. The family range "
                    + "result below proves no controller exists below W. For D>=W it "
                    + "characterizes each reachable prefix time and gives an operational "
                    + "same-raw-bit collision when E(t)+P<=D. It does not assert the full "
                    + "minimum clock alphabet.")),
            Describe.Lean(
                DescribeId.Create("deadline-prefix-time-range-and-collision"),
                DeclarationHandle.Create(Prefix + "deadline_prefix_time_range_and_collision"),
                H("Exact deadline times and a cross-controller collision"),
                StatementSource.FromAuthor(DeadlineStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A one-prefix delay table reaches each permitted time while the earliest "
                    + "tree keeps every other source within W. A controller below W "
                    + "contradicts the sharp waiting lower bound. For an eligible prefix, "
                    + "the zero-delay even source and one-period-delayed odd source have "
                    + "the same actual raw final read, although their source residues "
                    + "differ and their terminal times differ by P."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("deadline-family-operational-capacity"),
                DeclarationHandle.Create(Prefix + "deadline_family_operational_capacity"),
                H("One decoder for every deadline-family controller"),
                StatementSource.FromAuthor(CapacityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Labels are counted only when attained at a terminal time of a successful "
                    + "controller in the common-deadline family. For D below the sharp wait "
                    + "the family is empty. Otherwise any time-only encoder admitting one "
                    + "decoder for every controller and source uses at least 2^d plus the "
                    + "number of prefixes whose earliest time plus one period meets D. "
                    + "The explicit time tag records the prefix and delay parity, and one "
                    + "decoder combines it with the original uncorrected raw final bit. "
                    + "Its actual label image has exactly that cardinality. This proves "
                    + "the deadline-family operational part of source section 9.2; the "
                    + "closed-form slack staircase remains separate."))),
                DescribeRole.Theorem))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(string name, Formula domain, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, domain, Comma, Sp, Par(body));
    private static Formula Ex(string name, Formula domain, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, domain, Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Conj(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
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

    private static Formula DelayedStatement()
    {
        var a = F.Id("a"); var now = F.Id("now"); var r = F.Id("r");
        var p = F.Id("P"); var k = F.Id("K"); var read = F.Id("read"); var d = F.Id("d");
        var depth = Seq(d, Sp, Plus, Sp, D(1));
        var valid = Conj(Eqn(Call("mod", a, D(2)), D(0)),
            Conj(Seq(a, Sp, Plus, Sp, Call("pow", D(2), depth), Sp, Le, Sp, p),
                Conj(Seq(a, Sp, Le, Sp, r),
                    Seq(r, Sp, Lt, Sp, a, Sp, Plus, Sp, Call("pow", D(2), depth)))));
        var delayed = Call("execute", read, Call("delayedMidpoint", p, k, depth, a, now), now, r);
        var earliest = Call("execute", read, Call("midpoint", p, depth, a, now), now, r);
        var result = Conj(Eqn(Call("fst", delayed), Call("fst", earliest)),
            Eqn(Call("snd", delayed), Seq(Call("snd", earliest), Sp, Plus, Sp,
                p, Sp, Times, Sp, Call("K", Call("div", r, D(2))))));
        return Disp(All("P", N(), All("K", Seq(N(), Sp, To, Sp, N()),
            All("read", F.Id("NatToNatToFin2"), All("d", N(),
                Imp(Conj(Call("periodic", read, p), Call("thresholdLaw", read, p)),
                    All("a", N(), All("now", N(), All("r", N(), Imp(valid, result))))))))));
    }

    private static Formula DeadlineStatement()
    {
        var d = F.Id("d"); var b = F.Id("b"); var deadline = F.Id("D");
        var t = F.Id("t"); var u = F.Id("u"); var k = F.Id("k");
        var p = F.Id("p"); var p0 = F.Id("p0"); var p1 = F.Id("p1");
        var period = F.Id("P"); var wait = F.Id("W");
        var source = Seq(D(2), Sp, Times, Sp, t, Sp, Plus, Sp, u);
        var time = Seq(Call("E", t), Sp, Plus, Sp, period, Sp, Times, Sp, k);
        var family = Call("member", p, Call("F", deadline));
        var reachable = Ex("p", Call("Protocol", Seq(d, Sp, Plus, Sp, D(1))),
            Conj(family, Eqn(Call("N", p, source), time)));
        var range = All("t", N(), All("u", N(), All("k", N(), Imp(ValidPair(),
            Seq(Par(reachable), Sp, Iff, Sp, Par(Seq(time, Sp, Le, Sp, deadline)))))));
        var even = Seq(D(2), Sp, Times, Sp, t);
        var odd = Seq(even, Sp, Plus, Sp, D(1));
        var shifted = Eqn(Call("N", p1, odd), Seq(Call("N", p0, even), Sp, Plus, Sp, period));
        var sameRaw = Eqn(Call("Y", p0, even), Call("Y", p1, odd));
        var collisionBody = Conj(Call("member", p0, Call("F", deadline)),
            Conj(Call("member", p1, Call("F", deadline)), Conj(shifted, sameRaw)));
        var collision = Ex("p0", Call("Protocol", Seq(d, Sp, Plus, Sp, D(1))),
            Ex("p1", Call("Protocol", Seq(d, Sp, Plus, Sp, D(1))), collisionBody));
        var eligible = All("t", N(), Imp(Conj(Seq(t, Sp, Lt, Sp, Call("pow", D(2), d)),
            Seq(Call("E", t), Sp, Plus, Sp, period, Sp, Le, Sp, deadline)), collision));
        var body = Conj(Imp(Seq(deadline, Sp, Lt, Sp, wait), Call("empty", Call("F", deadline))),
            Conj(Imp(Seq(wait, Sp, Le, Sp, deadline), range),
                Imp(Seq(wait, Sp, Le, Sp, deadline), eligible)));
        return Disp(All("d", N(), All("b", Call("Fin", D(2)), All("D", N(), body))));
    }

    private static Formula CapacityStatement()
    {
        var d = F.Id("d"); var b = F.Id("b"); var deadline = F.Id("D");
        var baseCount = Call("pow", D(2), d);
        var count = Seq(baseCount, Sp, Plus, Sp,
            Call("card", Call("eligiblePrefixes", d, deadline)));
        var family = Call("deadlineFamily", d, b, deadline);
        var labels = Call("familyClockLabels", d, b, deadline, F.Id("phi"));
        var uniform = UniformDecoder(d, family, F.Id("phi"), F.Id("recover"));
        var lower = All("Z", F.Id("Type"), All("phi", Seq(N(), Sp, To, Sp, F.Id("Z")),
            All("recover", F.Id("ZToFin2ToNat"), Imp(uniform,
                Seq(count, Sp, Le, Sp, Call("card", labels))))));
        var upper = Conj(
            UniformDecoder(d, family, Call("clockTag", d), Call("tagDecode", d, b)),
            Eqn(Call("card", Call("familyClockLabels", d, b, deadline,
                Call("clockTag", d))), count));
        return Disp(All("d", N(), All("b", Call("Fin", D(2)), All("D", N(),
            Conj(Imp(Seq(deadline, Sp, Lt, Sp, Call("sharpWait", Seq(d, Sp, Plus, Sp, D(1)))),
                    Call("empty", family)),
                Imp(Seq(Call("sharpWait", Seq(d, Sp, Plus, Sp, D(1))), Sp, Le, Sp,
                    deadline), Conj(lower, upper)))))));
    }

    private static Formula UniformDecoder(Formula d, Formula family, Formula encoder, Formula decoder)
    {
        var p = F.Id("p"); var r = F.Id("r");
        var depth = Seq(d, Sp, Plus, Sp, D(1));
        var recovered = Call("apply", decoder, Call("apply", encoder, Call("N", p, r)),
            Call("Y", p, r));
        return All("p", Call("Protocol", depth), Imp(Call("member", p, family),
            All("r", N(), Imp(Seq(r, Sp, Lt, Sp, Call("pow", D(2), depth)),
                Eqn(recovered, r)))));
    }
}
