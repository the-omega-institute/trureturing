using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class ActualDyadicDeadlineSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive forward executions realize exactly the allowed dyadic final reads.",
        H("Actual Dyadic Deadline Support"),
        Blocks(
            Paragraph(Text("In the formulas, record(N,past) has event count N and read history past. Execution and ReachedRecord display their period index P while suppressing proof arguments. div and mod denote natural-number quotient and remainder; val unwraps finite values.")),
            Paragraph(Text(
                "A record consists of an event count and chronological time/raw-bit reads. "
                + "A policy takes only that record and chooses one forward event, a read, or a stop. "
                + "Execution denotes a finite physical run from a supplied record. No source or "
                + "future noise is an input to the policy. Fix d>=0, P=2^(d+1), a known b in Fin 2, "
                + "and E(t)=P-1+P wt(t)-2t. The original query parameter is j=d+1.")),
            Claim("execution-read-bounds", "execution_read_bounds", "Physical read order",
                                "For any positive period and any primitive run, events never decrease. The new "
                + "read trace has the read word's length, lies between the starting and reporting "
                + "clocks, and is pairwise ordered by time. Silent events after the final read "
                + "are permitted; the reporting clock need not be the final-read clock."),
            Claim("deadline-allowed-primitive-realization", "deadline_allowed_primitive_realization",
                "All-source causal realization",                 "If D>=sharpWait(d+1), t<2^d, u<2, and E(t)+PK<=D, one record-only policy "
                + "succeeds on every source in at most d+1 reads and reports by D. On source "
                + "2t+u it stops immediately after its literal final read at E(t)+PK."),
            Claim("actual-final-time-normal-form", "actual_final_time_normal_form",
                "Physical final-read normal form",                 "For every all-source successful policy under the dyadic read budget, each "
                + "bounded actual execution has exactly d pre-final reads. Their normalized "
                + "chronological fold is floor(r/2). The pre-final record is physically reached, "
                + "the policy reads there, and raw Y=(b+floor(N/P)+r mod 2) mod 2. Its literal "
                + "final time is E(floor(r/2))+PK for a nonnegative K and is no later than reporting."),
            Paragraph(Text(
                "DeadlineObservation(d,b,D,policy,r,past,N,Y) means that a correct primitive "
                + "execution from (0,[]) uses at most d+1 reads, ends its read trace in "
                + "past++[(N,Y)], and has N<=D. The all-source family requires such an "
                + "observation for every source. SupportedTime ranges over all policies in this "
                + "family and all observations with floor(r/2)=t. The deadline always bounds N, "
                + "rather than any later reporting event.")),
            Claim("actual-deadline-observation-normal-form", "actual_deadline_observation_normal_form",
                "Reached deadline observations",                 "For a policy in actualDeadlineFamily(d,b,D), each deadline observation has the "
                + "acquired prefix, reached pre-final record, "
                + "read action, literal raw bit, and nonnegative period-delay normal form. "
                + "The history in this statement is the history actually appearing in that observation."),
            Claim("actual-deadline-pair-realization", "actual_deadline_pair_realization",
                "One policy and one history for both siblings",                 "Assume D>=sharpWait(d+1), t<2^d, and E(t)+PK<=D for a natural K. "
                + "For each such allowed time, the same all-source policy and reached pre-final history "
                + "realize both final source bits. The writer's acquired prefix and read action "
                + "are fixed before either final bit is obtained. The final raw bit is retained."),
            Claim("actual-deadline-time-support", "actual_deadline_time_support",
                "Exact actual supported times",                 "With D at least the sharp common waiting bound and t<2^d, the supported times of each "
                + "prefix are exactly E(t)+PK with K a natural number and E(t)+PK<=D."),
            Claim("actual-raw-clock-quotient", "actual_raw_clock_quotient",
                "Raw clock quotient",                 "For t<2^d, floor((E(t)+PK)/P)=wt(t)+K. Thus raw clock parity is "
                + "(wt(t)+K) mod 2. The delay tag K mod 2 alone is a different quantity."),
            Claim("actual-deadline-raw-parity-support", "actual_deadline_raw_parity_support",
                "Singleton and double raw-parity support",                 "If D>=sharpWait(d+1) and t<2^d, the actual support B_D(t) contains "
                + "wt(t) mod 2. It contains both "
                + "parities exactly when E(t)+P<=D. Its definition ranges over all realizing "
                + "policies and their actual histories, rather than a fixed controller."),
            Claim("actual-deadline-staircase", "actual_deadline_staircase",
                "Exact primitive type staircase",                 "For D=sharpWait(d+1)+h, q counts 1<=i<=d+1 with 2^i<=h. There are "
                + "L=d+1-q singleton prefixes and M=2^(d+1)-(d+1)+q actual types. "
                + "Equivalently, n=2^d and M=2n-L. A singleton whose raw parity is one "
                + "still contributes one type. This counts actual supported types; it does "
                + "not determine the noisy hidden-schedule label minimum."))));

    private static DocumentBlock Claim(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Statement(declaration)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula x) => Seq(Left, Open, x, Right, Close);
    private static Formula Q(string names, Formula type, Formula body)
    {
        var binders = names.Split(' ');
        for (var i = binders.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, V(binders[i]), Colon, Sp, Par(type), Comma, Sp, Par(body));
        return body;
    }
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, Par(type), Comma, Sp, Par(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, Sp, Par(type), Sp, Mapsto, Sp, Par(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(V("let"), Sp, V(name), Colon, Sp, type, Sp, Colon, Eq, Sp, value, Semi, Sp, Par(body));
    private static Formula Arr(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, Par(b));
    private static Formula Pair(Formula a, Formula b) => Seq(Par(a), Sp, Times, Sp, Par(b));
    private static Formula Tup(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffF(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula And(params Formula[] parts)
    {
        var result = parts[parts.Length - 1];
        for (var i = parts.Length - 2; i >= 0; i--) result = Seq(Par(parts[i]), Sp, Land, Sp, Par(result));
        return result;
    }
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Add(Formula a, Formula b) => Seq(Par(a), Sp, Plus, Sp, Par(b));
    private static Formula Sub(Formula a, Formula b) => Seq(Par(a), Sp, Minus, Sp, Par(b));
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Sp, Cdot, Sp, Par(b));
    private static Formula Pow(Formula a, Formula b) => Seq(Par(a), Caret, Grp(b));
    private static Formula Div(Formula a, Formula b) => Call("div", a, b);
    private static Formula Mod(Formula a, Formula b) => Call("mod", a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Member(Formula x, Formula s) => Seq(x, Sp, InMacro, Sp, s);
    private static Formula Choice(Formula test, Formula yes, Formula no) =>
        Seq(V("if"), Sp, test, Sp, V("then"), Sp, yes, Sp, V("else"), Sp, no);

    private static Formula Statement(string declaration)
    {
        var d = V("d"); var b = V("b"); var p = V("P"); var deadline = V("D");
        var t = V("t"); var u = V("u"); var K = V("K"); var r = V("r");
        var policy = V("policy"); var word = V("word"); var terminal = V("terminal");
        var past = V("past"); var time = V("N"); var bit = V("bit");
        var depth = Add(d, D(1)); var period = Pow(D(2), depth); var prefixes = Pow(D(2), d);
        var readType = Pair(N, Fin(D(2))); var pastType = Call("List", readType);
        var wordType = Call("List", Fin(D(2))); var recordType = V("Record");
        var policyType = Arr(recordType, Call("Action", p));
        var empty = Call("record", D(0), Call("nil", readType));
        var resultType = Pair(recordType, Fin(p));
        var termRecord = Call("fst", terminal); var answer = Call("snd", terminal);
        var termEvents = Call("events", termRecord); var termReads = Call("reads", termRecord);
        var limit = Call("sharpWait", depth);
        var scheduledTime = Add(Call("earliestTime", d, t), Mul(period, K));
        var family = Call("actualDeadlineFamily", d, b, deadline, policy);
        var observation = Call("DeadlineObservation", d, b, deadline, policy, r, past, time, bit);
        var reached = Call("ReachedRecord", p, b, policy, r, empty, Call("record", time, past));
        var acquired = Call("acquiredPrefix", p, b, past, D(0));
        var raw = Eqn(Val(bit), Mod(Add(Add(Val(b), Div(time, p)), Mod(Val(r), D(2))), D(2)));
        var run = Call("Execution", p, b, policy, r, empty, word, terminal);
        var boundedCorrect = And(run, Leq(Call("length", word), depth), Eqn(answer, r));
        var sourceSuccess = Q("r", Fin(p), Ex("word", wordType, Ex("terminal", resultType, boundedCorrect)));
        var commonBounds = And(Leq(limit, deadline), Less(t, prefixes));
        Formula result;
        if (declaration == "execution_read_bounds")
        {
                var start = V("start"); var trace = V("trace"); var item = V("item");
                result = Q("P", N, Q("b", Fin(D(2)), Q("policy", policyType, Q("r", Fin(p),
                    Q("start", recordType, Q("word", wordType, Q("terminal", resultType,
                        Imp(And(Less(D(0), p), Call("Execution", p, b, policy, r, start, word, terminal)),
                            And(Leq(Call("events", start), termEvents), Ex("trace", pastType,
                                And(Eqn(termReads, Call("append", Call("reads", start), trace)),
                                    Eqn(Call("length", trace), Call("length", word)),
                                    Q("item", readType, Imp(Member(item, trace),
                                        And(Leq(Call("events", start), Call("fst", item)), Leq(Call("fst", item), termEvents)))),
                                    Call("Pairwise", trace, Fn("x", readType, Fn("y", readType,
                                        Leq(Call("fst", V("x")), Call("fst", V("y")))))))))))))))));
        }
        else if (declaration == "deadline_allowed_primitive_realization")
        {
                var before = V("before");
                var realization = Ex("r", Fin(p), Ex("word", wordType, Ex("terminal", resultType,
                    Ex("before", pastType, Ex("bit", Fin(D(2)), And(Eqn(Val(r), Add(Mul(D(2), t), u)), boundedCorrect,
                        Eqn(termEvents, Add(Call("earliestTime", d, t), Mul(p, K))),
                        Eqn(termReads, Call("append", before, Call("singletonList", Tup(termEvents, bit))))))))));
                result = Q("d", N, Q("b", Fin(D(2)), Q("D t u K", N,
                    Imp(And(commonBounds, Less(u, D(2)), Leq(scheduledTime, deadline)),
                        Let("P", N, period, Ex("policy", policyType,
                            And(Q("r", Fin(p), Ex("word", wordType, Ex("terminal", resultType,
                                And(boundedCorrect, Leq(termEvents, deadline))))), realization)))))));
        }
        else if (declaration == "actual_final_time_normal_form")
        {
                var normal = Ex("past", pastType, Ex("N", N, Ex("bit", Fin(D(2)), Ex("K", N,
                    And(Eqn(Call("length", past), d), Eqn(acquired, Div(Val(r), D(2))),
                        Eqn(termReads, Call("append", past, Call("singletonList", Tup(time, bit)))), reached,
                        Eqn(Call("policy", Call("record", time, past)), V("read")), raw,
                        Eqn(time, Add(Call("earliestTime", d, Div(Val(r), D(2))), Mul(p, K))),
                        Leq(time, termEvents))))));
                result = Q("P d", N, Q("b", Fin(D(2)), Q("policy", policyType,
                    Q("r", Fin(p), Q("word", wordType, Q("terminal", resultType,
                        Imp(And(Less(D(0), p), Eqn(p, period), sourceSuccess, run,
                            Leq(Call("length", word), depth)), normal)))))));
        }
        else if (declaration == "actual_deadline_observation_normal_form")
        {
                var observedNormal = And(Eqn(Call("length", past), d), Eqn(acquired, Div(Val(r), D(2))), reached,
                    Eqn(Call("policy", Call("record", time, past)), V("read")), raw,
                    Ex("K", N, Eqn(time, Add(Call("earliestTime", d, Div(Val(r), D(2))), Mul(p, K)))));
                result = Q("d", N, Q("b", Fin(D(2)), Q("D", N, Let("P", N, period,
                    Q("policy", policyType, Q("r", Fin(p), Q("past", pastType, Q("N", N, Q("bit", Fin(D(2)),
                        Imp(And(family, observation), observedNormal))))))))));
        }
        else if (declaration == "actual_deadline_pair_realization")
        {
                var pair = Q("u", Fin(D(2)), Ex("r", Fin(p), Ex("bit", Fin(D(2)),
                    And(Eqn(Val(r), Add(Mul(D(2), t), Val(u))), reached,
                        Eqn(Val(bit), Mod(Add(Add(Val(b), Div(time, p)), Val(u)), D(2))), observation))));
                result = Q("d", N, Q("b", Fin(D(2)), Q("D t K", N,
                    Imp(And(commonBounds, Leq(scheduledTime, deadline)), Let("P", N, period,
                        Let("N", N, scheduledTime, Ex("policy", policyType, And(family,
                            Ex("past", pastType, And(Eqn(Call("length", past), d), Eqn(acquired, t),
                                Eqn(Call("policy", Call("record", time, past)), V("read")), pair))))))))));
        }
        else if (declaration == "actual_deadline_time_support")
        {
                result = Q("d", N, Q("b", Fin(D(2)), Q("D t N", N, Imp(commonBounds,
                    IffF(Call("actualSupportedTime", d, b, deadline, t, time),
                        Ex("K", N, And(Eqn(time, scheduledTime), Leq(time, deadline))))))));
        }
        else if (declaration == "actual_raw_clock_quotient")
        {
                result = Q("d t K", N, Imp(Less(t, prefixes),
                    Eqn(Div(scheduledTime, period), Add(Call("length", Call("bitIndices", t)), K))));
        }
        else if (declaration == "actual_deadline_raw_parity_support")
        {
                result = Q("d", N, Q("b", Fin(D(2)), Q("D t", N, Q("nu", Fin(D(2)), Imp(commonBounds,
                    IffF(Member(V("nu"), Call("actualParitySupport", d, b, deadline, t)),
                        Or(Eqn(Val(V("nu")), Mod(Call("length", Call("bitIndices", t)), D(2))),
                            Leq(Add(Call("earliestTime", d, t), period), deadline))))))));
        }
        else if (declaration == "actual_deadline_staircase")
        {
                var q = V("q"); var paritySet = Call("actualParitySupport", d, b, deadline, Val(t));
                var parity = Seq(Langle, Mod(Call("length", Call("bitIndices", Val(t))), D(2)), Rangle, Colon, Fin(D(2)));
                var qSet = Call("filter", Call("Icc", D(1), depth), Fn("i", N, Leq(Pow(D(2), V("i")), V("h"))));
                result = Q("d h", N, Q("b", Fin(D(2)), Let("D", N, Add(limit, V("h")),
                    Let("q", Call("Finset", N), qSet,
                        And(Q("t", Fin(prefixes), Eqn(paritySet,
                                Choice(Member(t, Call("eligiblePrefixes", d, deadline)), Call("univ", Fin(D(2))), Call("singleton", parity)))),
                            Eqn(Card(Call("filter", Call("univ", Fin(prefixes)), Fn("t", Fin(prefixes), Eqn(Card(paritySet), D(1))))),
                                Sub(depth, Card(q))),
                            Eqn(Card(Call("actualTypes", d, b, deadline)), Add(Sub(period, depth), Card(q))))))));
        }
        else
        {
            throw new System.InvalidOperationException("Unknown primitive support statement.");
        }
        return Disp(result);
    }
}
