using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class RawEndpointPeelingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw leaf peeling follows one target while separating branch and absent reply groups, and completes each selected source with its entire labelled leaf frontier.",
        H("Raw Endpoint Leaf Peeling"),
        Blocks(
            Paragraph(Text("The sources and four replies are the actual ordered binary trees and their original readout. A strategy uses a single deterministic policy, starts with an empty history on every source, and terminates correctly on every finite source. Fees count the distinct addresses actually requested. L(U) is the existing leafAddresses(U).")),
            Def("Peels", "Safe target-leaf lists",
                "For a finite family F, target z, survivor set S and finite address list qs, Peels recursively requires each address to be a leaf of F(z). The branch and absent response groups in S each have at most one member. The next survivor set is the group reporting the target's actual reply. At the end every survivor is z. When S initially contains z, it retains z throughout. For a nonconflicting family, every leaf reply matches the target label, so the recursion deletes exactly the two nonleaf groups and leaves no competitor at the end."),
            Def("peelController", "Actual raw peeling controller",
                "The controller actually requests the next address. A target reply continues with its response group. A different reply whose group is a singleton starts that source's complete leaf verifier with a fresh logical history; any other reply starts the existing acquisition fallback. Exhausting the list starts the target's complete verifier. The verifier accepts only the complete matching labelled frontier, and mismatches enter acquisition. The paid set comes from the resulting execution history."),
            Describe.Lean(DescribeId.Create("raw-endpoint-peeling-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Endpoint criterion and exact execution bills"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For k at least one, m=2k+1 and n=3k+13. Fk is the existing nested-compensation family transported from Unit plus Fin(k) plus Fin(k) to Fin(m) by Fintype.equivFin. This bijection changes only the member indices. All members are positive, distinct, nonconflicting and have n leaves. The target z ranges over every member. The indicator is one when its equality holds and zero otherwise; subtraction is natural subtraction.")),
                    Paragraph(Text("C(pi,U), J(pi,U) and T(pi,U) denote the existing cost, paid terminal-history set and terminal outcome. CostVector(pi,Fk,z,n) abbreviates the displayed universal endpoint equation C(pi,Fk(i))=n+1-indicator(i=z). c(Fk,z,qs) is peelController(Fk,z,univ,qs), O(c,U) is controllerOutcome(c,U), and P(c) is controllerPolicy(c). First(qs,Fk,i) is List.find? with the actual nonleaf predicate chi(readout(a,Fk(i)))=1. Thus some(q) identifies the first exit address, including in lists with repeated requests.")),
                    Paragraph(Text("Necessity uses a recursive actual-response route whose costs are no greater than those of the given strategy. Zero target excess makes every query on its path a target leaf. Each branch or absent child has zero remaining excess on all its members; nonconflict forces such a child to be a singleton. Following the target child therefore yields a safe finite list. Conversely the listed controller follows matching leaves until the first nonleaf response, selects that unique member, and verifies its complete frontier. Earlier queries are that member's leaves; its exit is its sole nonleaf. On the target all route queries are leaves. Complete verification yields exactly the asserted paid sets and endpoint costs on every family member. The existing execution contract connects every controller outcome to the policy's actual finite run on every source."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("raw-endpoint-peeling-" + name.ToLowerInvariant()),
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
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, Equal, Sp, b);

    private static Formula ResultFormula()
    {
        Formula k = V("k"), z = V("z"), i = V("i"), q = V("q"), qs = V("qs"), pi = V("pi");
        Formula family = V("Fk"), n = V("n"), m = V("m");
        Formula indices = Call("Fin", m), source = Call("Source"), address = Call("Address");
        Formula tree(Formula j) => Call("Fk", j);
        Formula leaves(Formula j) => Call("L", tree(j));
        Formula paid(Formula j) => Call("J", pi, tree(j));
        Formula costs = Call("CostVector", pi, family, z, n);
        Formula peels = Call("Peels", family, z, V("univ"), qs);
        Formula controller = Call("c", family, z, qs);
        Formula exits = All("i", indices, Imp(Seq(i, Sp, Neq, Sp, z), Some("q", address, And(
            Eq(Call("First", qs, family, i), Call("some", q)),
            Seq(Neg, Sp, Par(Seq(q, Sp, InMacro, Sp, leaves(i)))),
            Eq(paid(i), Seq(leaves(i), Sp, Cup, Sp, Call("singleton", q)))))));
        Formula bills = Some("pi", Call("Strategy"), And(
            Eq(Call("policy", pi), Call("P", controller)),
            All("U", source, Eq(Call("T", pi, V("U")), Call("O", controller, V("U")))),
            costs, Eq(paid(z), leaves(z)), exits));
        Formula criterion = Seq(Par(Some("pi", Call("Strategy"), costs)), Sp, Iff, Sp,
            Par(Some("qs", Call("List", address), peels)));
        return Disp(All("k", V("Nat"), Imp(Seq(D(1), Sp, Leq, Sp, k), All("z", indices,
            And(criterion, All("qs", Call("List", address), Imp(peels, bills)))))));
    }
}
