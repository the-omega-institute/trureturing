using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;
internal sealed class ActualDyadicDeadlineRepairMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original causal deadline repair contract has the exact mixed-demand cyclic capacity.",
        H("Actual Dyadic Deadline Repair Minimum"),
        Blocks(
            Paragraph(Text("In the formulas, div denotes natural-number division, real is the real coercion, and record(N,past) has event count N and read history past. The displayed writer and decoder condition expands CommonRepairFeasible. In support ranking, equivFin bijects each finite parity support with the ranks below its cardinality.")),
            Paragraph(Text(
                "Let P=2^(d+1), n=2^d, and b be a known bit. A primitive policy chooses only "
                + "forward events, noiseless nondisturbing reads, and stops from its acquired record. "
                + "The deadline family includes every deterministic policy successful on every "
                + "source in at most d+1 reads with literal final query N<=D. Reporting delay "
                + "is unrestricted. A supported type (t,nu) retains the actual raw parity "
                + "nu=floor(N/P) mod 2 and the phase center P-1-2t.")),
            Describe.Lean(DescribeId.Create("actual-demand"), DeclarationHandle.Create(Prefix + "actualDemand"),
                H("Actual support demand"), StatementSource.FromAuthor(Statement("actualDemand")), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The demand at t is the cardinality of its actual raw-parity support. "
                    + "For D>=sharpWait(d+1) and t<n this is one or two."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supported-type-rank-equiv"),
                DeclarationHandle.Create(Prefix + "supportedTypeRankEquiv"), H("Lossless support ranking"),
                StatementSource.FromAuthor(Statement("supportedTypeRankEquiv")), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "There is a prefix-preserving equivalence between actual supported raw types "
                    + "and demand-ranked types. Each finite raw-parity support is bijected with "
                    + "the ranks below its cardinality. Both inverse laws hold. A singleton "
                    + "has rank zero even when its sole raw parity is one. Double support has "
                    + "two ranks; unranking recovers the actual raw parity."))), DescribeRole.Definition),
            Claim("actual-phase-overlap-near", "actual_phase_overlap_near", "Exact closed error shell",
                "Assume D>=sharpWait(d+1), m>=2, and m-1<=eps<m. Two prefix phase balls "
                + "intersect exactly when the circular integer distance of their prefixes is "
                + "less than m. A realized all-source schedule supplies the phase-distance "
                + "scaling by two. Closed-ball intersection includes equality at eps=m-1. "
                + "The circular seam and equal prefixes are included."),
            Claim("actual-supported-coloring-iff", "actual_supported_coloring_iff", "Both coloring transports",
                "Under the same deadline and error-shell assumptions, for any label type Z "
                + "the actual supported types admit a proper Z-coloring exactly when the "
                + "ranked mixed-demand cyclic graph does. The equivalence preserves prefixes "
                + "and distinct supported raw types in both directions. Unsupported pairs "
                + "are given an existing supported color when extending to a total function. "
                + "Different raw parities at the same prefix remain distinct adjacent types."),
            Claim("original-window-size", "original_window_size", "Original prefix-window size",
                "For j>=2 and m>=2, the original logarithmic size condition "
                + "3+floor(log2(m))<=j implies 2m<2^(j-1)."),
            Claim("original-operational-minimum", "original_operational_minimum", "Exact original shared-decoder minimum",
                "For j>=2, h>=0, known b, P=2^j, n=2^(j-1), and D=(j-1)P+1+h, "
                + "assume m>=2, m-1<=eps<m, j>=3+floor(log2(m)), n=ma+rho, rho<m, "
                + "and a>=2rho. Put q=#{1<=i<=j:2^i<=h} and L=j-q. The least alphabet "
                + "cardinality is max(2m,ceil((2n-L)/a))=2m+indicator(L<2rho). "
                + "The logarithmic hypothesis supplies n>2m and a consecutive m-prefix "
                + "window with double demand; these are consequences, not extra premises. "
                + "Feasibility means a writer receiving only policy and actual pre-final record "
                + "and one common receiver recovering every source for every deadline-family "
                + "policy and every closed phase error. The label precedes the final read and "
                + "future error. The receiver sees only phase, exact raw Y, label, and fixed "
                + "public parameters; policy, N, and past reads are hidden. All-history label "
                + "separation and the two coloring transports give both attainment and the "
                + "universal lower bound."))));
    private static DocumentBlock Claim(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Statement(declaration)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
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
    private static Formula Add(Formula a, Formula b) => Seq(Par(a), Sp, Plus, Sp, Par(b));
    private static Formula Sub(Formula a, Formula b) => Seq(Par(a), Sp, Minus, Sp, Par(b));
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Sp, Cdot, Sp, Par(b));
    private static Formula Pow(Formula a, Formula b) => Seq(Par(a), Caret, Grp(b));
    private static Formula Div(Formula a, Formula b) => Call("div", a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Member(Formula x, Formula s) => Seq(x, Sp, InMacro, Sp, s);
    private static Formula Set(string name, Formula type, Formula body) =>
        Seq(OpenBrace, V(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Choice(Formula test, Formula yes, Formula no) =>
        Seq(V("if"), Sp, test, Sp, V("then"), Sp, yes, Sp, V("else"), Sp, no);

    private static Formula Statement(string declaration)
    {
        var d = V("d"); var b = V("b"); var deadline = V("D"); var m = V("m");
        var eps = V("eps"); var t = V("t"); var x = V("x"); var v = V("v");
        var period = Pow(D(2), Add(d, D(1))); var prefixes = Pow(D(2), d);
        var rawType = Pair(Fin(prefixes), Fin(D(2)));
        var demand = Call("actualDemand", d, b, deadline);
        var vertex = Call("Vertex", demand);
        var shell = And(Leq(Call("sharpWait", Add(d, D(1))), deadline), Leq(D(2), m),
            Leq(Sub(Call("real", m), D(1)), eps), Less(eps, Call("real", m)));
        var overlap = Ex("phase", Call("AddCircle", Call("real", period)),
            And(Leq(Call("dist", V("phase"), Call("prefixPhase", d, V("i"))), eps),
                Leq(Call("dist", V("phase"), Call("prefixPhase", d, V("j"))), eps)));
        var colors = Ex("color", Arr(rawType, V("Z")), Call("ActualTypeColoring", d, b, deadline, eps, V("color")));
        var rankedColors = Ex("color", Arr(vertex, V("Z")), Call("Proper", m, demand, V("color")));
        Formula result;
        if (declaration == "actualDemand")
        {
                result = Q("d", N, Q("b", Fin(D(2)), Q("D", N, Q("t", Fin(prefixes),
                    Eqn(Call("actualDemand", d, b, deadline, t), Card(Call("actualParitySupport", d, b, deadline, Val(t))))))));
        }
        else if (declaration == "supportedTypeRankEquiv")
        {
                var source = Set("x", rawType, Member(x, Call("actualTypes", d, b, deadline)));
                var equiv = Call("supportedTypeRankEquiv", d, b, deadline);
                var prefix = Call("fst", Val(x)); var parity = Call("snd", Val(x));
                var paritySupport = Call("actualParitySupport", d, b, deadline, Val(prefix));
                var rank = Call("equivFin", paritySupport);
                var supportedParity = Seq(Langle, parity, Rangle, Colon,
                    Set("nu", Fin(D(2)), Member(V("nu"), paritySupport)));
                var unrank = Call("equivFin", Call("actualParitySupport", d, b, deadline, Val(Call("fst", v))));
                var inverseValue = Seq(Langle,
                    Tup(Call("fst", v), Val(Call("apply", Call("symm", unrank), Call("snd", v)))),
                    Rangle, Colon, source);
                result = Q("d", N, Q("b", Fin(D(2)), Q("D", N,
                    And(Seq(equiv, Colon, Sp, Call("Equiv", source, vertex)),
                        Q("x", source, Eqn(Call("apply", equiv, x), Tup(prefix, Call("apply", rank, supportedParity)))),
                        Q("v", vertex, Eqn(Call("apply", Call("symm", equiv), v), inverseValue)),
                        Q("x", source, Eqn(Call("apply", Call("symm", equiv), Call("apply", equiv, x)), x)),
                        Q("v", vertex, Eqn(Call("apply", equiv, Call("apply", Call("symm", equiv), v)), v))))));
        }
        else if (declaration == "actual_phase_overlap_near")
        {
                result = Q("d", N, Seq(Forall, Sp, Underscore, Colon, Sp, Fin(D(2)), Comma, Sp,
                    Par(Q("D m", N, Q("eps", R, Q("i j", Fin(prefixes),
                        Imp(shell, IffF(overlap, Call("Near", m, V("i"), V("j"))))))))));
        }
        else if (declaration == "actual_supported_coloring_iff")
        {
                result = Q("Z", V("Type"), Q("d", N, Q("b", Fin(D(2)), Q("D m", N, Q("eps", R,
                    Imp(shell, IffF(colors, rankedColors)))))));
        }
        else if (declaration == "original_window_size")
        {
                var j = V("j");
                result = Q("j m", N, Imp(And(Leq(D(2), j), Leq(D(2), m),
                    Leq(Add(D(3), Call("log2", m)), j)),
                    Less(Mul(D(2), m), Pow(D(2), Sub(j, D(1))))));
        }
        else if (declaration == "original_operational_minimum")
        {
                var j = V("j"); var h = V("h"); var a = V("a"); var rho = V("rho");
                var n = V("n"); var L = V("L"); var capacity = V("capacity"); var c = V("c");
                var policyType = Arr(V("Record"), Call("Action", period));
                var writerType = Arr(policyType, Arr(V("Record"), Fin(c)));
                var receiverType = Arr(Call("AddCircle", Call("real", period)), Arr(Fin(D(2)), Arr(Fin(c), N)));
                var pastType = Call("List", Pair(N, Fin(D(2))));
                var observations = Q("policy", policyType,
                    Imp(Call("actualDeadlineFamily", d, b, deadline, V("policy")),
                        Q("r", Fin(period), Q("past", pastType, Q("N", N, Q("bit", Fin(D(2)),
                            Imp(Call("DeadlineObservation", d, b, deadline, V("policy"), V("r"), V("past"), V("N"), V("bit")),
                                Q("phase", Call("AddCircle", Call("real", period)),
                                    Imp(Leq(Call("dist", V("phase"), Call("terminalPhase", V("r"))), eps),
                                        Eqn(Call("decoder", V("phase"), V("bit"),
                                            Call("writer", V("policy"), Call("record", V("N"), V("past")))), Val(V("r"))))))))))));
                var feasible = Set("c", N, Ex("writer", writerType, Ex("decoder", receiverType, observations)));
                var qCount = Card(Set("i", N, And(Leq(D(1), V("i")), Leq(V("i"), j), Leq(Pow(D(2), V("i")), h))));
                var conclusion = Let("d", N, Sub(j, D(1)), Let("n", N, prefixes,
                    Let("D", N, Add(Add(Mul(Sub(j, D(1)), Pow(D(2), j)), D(1)), h),
                        Let("q", N, qCount, Let("L", N, Sub(j, V("q")),
                            Let("capacity", N, Call("max", Mul(D(2), m), Div(Sub(Add(Sub(Mul(D(2), n), L), a), D(1)), a)),
                                And(Call("IsLeast", feasible, capacity), Eqn(capacity,
                                    Add(Mul(D(2), m), Choice(Less(L, Mul(D(2), rho)), D(1), D(0)))))))))));
                result = Q("j h m a rho", N, Q("b", Fin(D(2)), Q("eps", R,
                    Imp(And(Leq(D(2), j), Leq(D(2), m), Leq(Sub(Call("real", m), D(1)), eps), Less(eps, Call("real", m)),
                        Leq(Add(D(3), Call("log2", m)), j), Eqn(Pow(D(2), Sub(j, D(1))), Add(Mul(m, a), rho)),
                        Less(rho, m), Leq(Mul(D(2), rho), a)), conclusion))));
        }
        else
        {
            throw new System.InvalidOperationException("Unknown deadline minimum statement.");
        }
        return Disp(result);
    }
}
