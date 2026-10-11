using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class ActualDyadicDeadlineLabelSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Budget/ActualDyadicDeadlineLabelSupport.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Causal labels over all histories are equivalent to coloring actual supported types.",
        H("All-History Deadline Label Supports"),
        Blocks(
            Paragraph(Text("In the formulas, record(N,past) has event count N and read history past. div and mod denote natural-number quotient and remainder, real is the real coercion, and angle brackets construct the indicated finite value. The expanded feasibility condition is CommonRepairFeasible.")),
            Paragraph(Text(
                "Fix d>=0, P=2^(d+1), known b, a deadline D, and a closed error radius eps. "
                + "The primitive deadline family requires correct acquisition on every source "
                + "within d+1 reads and literal last-read time at most D. A type consists of "
                + "a prefix t and raw clock parity nu=floor(N/P) mod 2 that is realized by "
                + "some member of this entire family. Its circular phase center is P-1-2t. "
                + "Two distinct supported types conflict when their closed phase balls intersect. "
                + "Different parities at the same prefix have the same phase center.")),
            Claim("actual-type-coloring-common-decoder", "actual_type_coloring_common_decoder",
                "Causal writing and one shared receiver",
                "A proper coloring of the supported types yields a record-only writer. It "
                + "normalizes and folds acquired pre-final reads to obtain t, computes nu from "
                + "the pre-final event count, and emits the color of (t,nu). One receiver takes "
                + "only noisy phase, the exact final raw bit, and that label; d,b,D,eps and "
                + "the coloring are fixed public parameters. The receiver selects a compatible "
                + "type using phase and label, then returns 2t+((Y+b+nu) mod 2). Properness "
                + "makes the type unique. This receiver sees neither the policy, N, nor past "
                + "reads, and works for all deadline-family policies, sources and closed errors."),
            Paragraph(Text(
                "A causal writer may depend on its policy and complete acquired pre-final "
                + "record, but receives no unseen final source bit or future error. A type's "
                + "label support is the set of labels emitted by every realizing policy and "
                + "every actual pre-final history for that type. It is not the image of a "
                + "single fixed policy or a chosen representative history.")),
            Claim("actual-common-decoder-support-separation", "actual_common_decoder_support_separation",
                "Nonempty and disjoint all-history supports",
                "Every supported type has a nonempty label support. If one receiver recovers "
                + "all policies and closed errors, conflicting types have disjoint supports. "
                + "For any shared label, sibling replay under each realizing policy preserves "
                + "the same reached pre-final record and chooses u=(b+nu) mod 2, giving raw "
                + "Y=0. A shared closed-ball phase then gives the receiver identical inputs "
                + "with different sources. This includes a single prefix with different nu."),
            Claim("actual-all-history-coloring-iff", "actual_all_history_coloring_iff",
                "Exact operational coloring equivalence",
                "For any label type Z, an all-history causal writer with one common receiver "
                + "exists exactly when the actual supported types admit a proper Z-coloring. "
                + "Necessity selects one label from each nonempty support; disjointness "
                + "makes the selection proper. Sufficiency constructs the causal writer "
                + "and shared receiver described above. The criterion is expressed using "
                + "actual closed-ball intersections. It does not itself identify the integer "
                + "distance graph or compute its mixed-demand chromatic minimum."))));

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
    private static Formula Arr(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, Par(b));
    private static Formula Pair(Formula a, Formula b) => Seq(Par(a), Sp, Times, Sp, Par(b));
    private static Formula Tup(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffF(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula And(params Formula[] parts)
    {
        var result = parts[parts.Length - 1];
        for (var i = parts.Length - 2; i >= 0; i--) result = Seq(Par(parts[i]), Sp, Land, Sp, Par(result));
        return result;
    }
    private static Formula Add(Formula a, Formula b) => Seq(Par(a), Sp, Plus, Sp, Par(b));
    private static Formula Pow(Formula a, Formula b) => Seq(Par(a), Caret, Grp(b));
    private static Formula Div(Formula a, Formula b) => Call("div", a, b);
    private static Formula Mod(Formula a, Formula b) => Call("mod", a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Member(Formula x, Formula s) => Seq(x, Sp, InMacro, Sp, s);
    private static Formula Feasible(Formula d, Formula b, Formula deadline, Formula eps, Formula writer, Formula z)
    {
        var period = Pow(D(2), Add(d, D(1))); var circle = Call("AddCircle", Call("real", period));
        var policyType = Arr(V("Record"), Call("Action", period));
        var pastType = Call("List", Pair(N, Fin(D(2))));
        return Ex("decoder", Arr(circle, Arr(Fin(D(2)), Arr(z, N))),
            Q("policy", policyType, Imp(Call("actualDeadlineFamily", d, b, deadline, V("policy")),
                Q("r", Fin(period), Q("past", pastType, Q("N", N, Q("bit", Fin(D(2)),
                    Imp(Call("DeadlineObservation", d, b, deadline, V("policy"), V("r"), V("past"), V("N"), V("bit")),
                        Q("phase", circle, Imp(Leq(Call("dist", V("phase"), Call("terminalPhase", V("r"))), eps),
                            Eqn(Call("decoder", V("phase"), V("bit"), Call("apply", writer, V("policy"),
                                Call("record", V("N"), V("past")))), Val(V("r")))))))))))));
    }
    private static Formula Statement(string declaration)
    {
        var d = V("d"); var b = V("b"); var deadline = V("D"); var eps = V("eps"); var z = V("Z");
        var period = Pow(D(2), Add(d, D(1))); var prefixes = Pow(D(2), d);
        var rawType = Pair(Fin(prefixes), Fin(D(2)));
        var policyType = Arr(V("Record"), Call("Action", period));
        var writerType = Arr(policyType, Arr(V("Record"), z)); var writer = V("writer"); var color = V("color");
        var proper = Call("ActualTypeColoring", d, b, deadline, eps, color);
        var feasible = Feasible(d, b, deadline, eps, writer, z);
        var x = V("x"); var y = V("y"); var types = Call("actualTypes", d, b, deadline);
        var overlap = Ex("phase", Call("AddCircle", Call("real", period)),
            And(Leq(Call("dist", V("phase"), Call("prefixPhase", d, Call("fst", x))), eps),
                Leq(Call("dist", V("phase"), Call("prefixPhase", d, Call("fst", y))), eps)));
        Formula result;
        if (declaration == "actual_type_coloring_common_decoder")
        {
                var record = V("record");
                var prefix = Seq(Langle, Mod(Call("acquiredPrefix", period, b, Call("reads", record), D(0)), prefixes),
                    Rangle, Colon, Fin(prefixes));
                var parity = Seq(Langle, Mod(Div(Call("events", record), period), D(2)), Rangle, Colon, Fin(D(2)));
                result = Q("color", Arr(rawType, z), Imp(proper, Ex("writer", writerType,
                    And(Q("policy", policyType, Q("record", V("Record"),
                        Eqn(Call("writer", V("policy"), record), Call("color", Tup(prefix, parity))))), feasible))));
        }
        else if (declaration == "actual_common_decoder_support_separation")
        {
                var supportX = Call("actualLabelSupport", d, b, deadline, writer, x);
                var supportY = Call("actualLabelSupport", d, b, deadline, writer, y);
                result = Q("writer", writerType, Imp(feasible,
                    And(Q("x", rawType, Imp(Member(x, types), Call("Nonempty", supportX))),
                        Q("x y", rawType, Imp(And(Member(x, types), Member(y, types), Ne(x, y), overlap),
                            Call("Disjoint", supportX, supportY))))));
        }
        else if (declaration == "actual_all_history_coloring_iff")
        {
                result = IffF(Ex("writer", writerType, feasible), Ex("color", Arr(rawType, z), proper));
        }
        else
        {
            throw new System.InvalidOperationException("Unknown all-history label statement.");
        }
        return Disp(Q("Z", V("Type"), Q("d", N, Q("b", Fin(D(2)), Q("D", N, Q("eps", R, result))))));
    }
}
