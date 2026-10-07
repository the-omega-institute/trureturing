using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class CoarseEndpointPeelingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A target attains the coarse endpoint precisely when its leaves separate at most one merged nonleaf competitor at a time.",
        H("Coarse Endpoint Leaf Peeling"),
        Blocks(
            Paragraph(Text("The sources are all finite nonempty ordered binary trees with Boolean leaf labels. Positive means membership in the third substitution image. A Strategy has one deterministic history policy, an empty initial history on every source, and a correct finite run on every source. Fees count distinct actual addresses. kappa preserves the two leaf labels and merges branch and absent into none. CoarseObservable(p) means Function.FactorsThrough p kappa_hist: for all raw histories h and g, kappa_hist(h)=kappa_hist(g) implies p(h)=p(g), including histories that no actual source realizes.")),
            Def("Peels", "Safe merged-nonleaf peeling",
                "For family F, target z and current survivor set S, every listed address q must be a leaf of F(z). The existing coarse fiber at none has cardinality at most one. Continue with the fiber at the target's leaf label. The empty list requires S to be contained in {z}. Starting with all members retains the target throughout; removing z from each survivor set gives the competitor-only formulation. Nonconflict makes any competitor that is still a leaf report the same label, so each step deletes exactly the merged branch-or-absent group. The target never belongs to that group."),
            Def("peelRoute", "Finite actual coarse route",
                "The passive protocol requests the listed addresses in order while the actual coarse reply equals the target's label. A different reply immediately stops the route. Repeated addresses remain logical requests, with distinct-address charging supplied by the common completion."),
            Def("peelDecode", "Reached singleton selection",
                "Replay the route history from its current survivor set. Matching replies update that set to the existing coarse fiber. A different reply selects its unique member when that response fiber is a singleton. Exhausting the list selects z. A malformed query address, incomplete history or non-singleton different response selects no member. The common completion verifies a selected member's complete leaf frontier and starts acquisition when no member is selected or verification fails."),
            Describe.Lean(DescribeId.Create("coarse-endpoint-peeling-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Endpoint equivalence and exact paid sets"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every k at least one, the index set is Fin(2k+1). F(k,i) is Scale38NestedCompensation.family(k) transported through Fintype.equivFin from Unit plus Fin(k) plus Fin(k); F(k) denotes the whole function on this index set. Every member is positive, distinct and has 3k+13 leaves; every pair is nonconflicting. The target z ranges over all members. The indicator equals one precisely when i=z, and subtraction is natural subtraction.")),
                    Paragraph(Text("L(U) denotes leafAddresses(U), C(pi,U) denotes cost(pi,U), and J(pi,U) denotes paid(terminal(pi,U).1). First(qs,F(k),i) is List.find? on the predicate leafLabel(F(k,i),a)=none, so it names the first nonleaf exit even when qs repeats addresses. P(F(k),z,qs) is the policy obtained by compileRaw with peelRoute and peelDecode, evaluated on encodeHistory(kappa_hist(h)). The equality with this policy connects the precise bills to the actual common completion, including its globally correct fallback.")),
                    Paragraph(Text("A baseline-cost target must request exactly its leaves. A surviving competitor shares the target's coarse prefix, and the same next query therefore extends both actual histories. If two competitors report none there, each has paid a nonleaf on their common coarse prefix. The common-history obstruction forces one to pay at least two nonleaves, contrary to endpoint costs. At the target's terminal history no different member can remain, since the same obstruction supplies a strictly later divergence. Following the target's finite terminal trace gives the safe list.")),
                    Paragraph(Text("Conversely a safe route selects the unique exiting competitor or the target. Requests before an exit are that member's own leaves; the exit is its sole nonleaf. The complete verifier obtains every leaf of the selected member. The common completion's paid-set union therefore gives L(Z) on the target and L(U) union the singleton exit on every competitor, and hence the stated costs."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("coarse-endpoint-peeling-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) =>
        Seq(xs.Select((x, i) => i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);

    private static Formula ResultFormula()
    {
        Formula k = V("k"), z = V("z"), i = V("i"), q = V("q"), qs = V("qs"), pi = V("pi");
        Formula family = Call("F", k);
        Formula m = Seq(D(2), Sp, Cdot, Sp, k, Sp, Plus, Sp, D(1));
        Formula indices = Call("Fin", m), address = Call("Address");
        Formula tree(Formula j) => Call("F", k, j);
        Formula leaves(Formula j) => Call("L", tree(j));
        Formula paid(Formula j) => Call("J", pi, tree(j));
        Formula coarse = Call("CoarseObservable", Call("policy", pi));
        Formula costs = All("i", indices, Eq(Call("C", pi, tree(i)),
            Seq(D(3), Sp, Cdot, Sp, k, Sp, Plus, Sp, D(1,4), Sp, Minus, Sp,
                Call("indicator", Eq(i, z)))));
        Formula peels = Call("Peels", family, z, V("univ"), qs);
        Formula exits = All("i", indices, Imp(Seq(i, Sp, Neq, Sp, z), Some("q", address, And(
            Eq(Call("First", qs, family, i), Call("some", q)),
            Seq(Neg, Sp, Par(Seq(q, Sp, InMacro, Sp, leaves(i)))),
            Eq(paid(i), Seq(leaves(i), Sp, Cup, Sp, Call("singleton", q)))))));
        Formula bills = Some("pi", Call("Strategy"), And(
            Eq(Call("policy", pi), Call("P", family, z, qs)), coarse,
            costs, Eq(paid(z), leaves(z)), exits));
        Formula criterion = Seq(Par(Some("pi", Call("Strategy"), And(coarse, costs))), Sp, Iff, Sp,
            Par(Some("qs", Call("List", address), peels)));
        return Disp(All("k", V("Nat"), Imp(Seq(D(1), Sp, Leq, Sp, k), All("z", indices,
            And(criterion, All("qs", Call("List", address), Imp(peels, bills)))))));
    }
}
