using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class CoarseMinimaxBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CoarseMinimaxBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniformly one-excess coarse controller supplies a safe endpoint route, forcing two excess queries when the endpoint spectrum is empty.",
        H("Coarse Controllers and the Minimax Lower Bound"),
        Blocks(Describe.Lean(DescribeId.Create("coarse-minimax-bridge-result"),
            DeclarationHandle.Create(Prefix + "result"), H("Universal endpoint bridge and lower bound"),
            StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For k at least one, I(k)=Fin(2k+1). Let e be Fintype.equivFin from Unit plus Fin(k) plus Fin(k), and let F(k,i) be the existing Scale38NestedCompensation.family(k,e.symm(i)). Every member has n=3k+13 leaves. Strategy means one deterministic policy that terminates and correctly decides positivity on every nonempty finite ordered labelled full binary tree. CoarseObservable means that the policy depends only on its chronological history with branch and absent merged into none, retaining both distinct leaf labels. C(pi,U) is the number of different addresses actually requested.")),
                Paragraph(Text("Safe(k,z,qs) denotes CoarseEndpointPeeling.Peels(F(k),z,univ,qs). Each address is a leaf of the eventual target, its merged nonleaf group has at most one surviving member, and the final survivor set is contained in the target singleton. The first conjunct quantifies over every coarse Strategy with a uniform cost bound n+1. It produces an actual finite address list and a target with this safety property. The existing peeling theorem realizes the list as a globally correct coarse endpoint strategy with exact paid sets.")),
                Paragraph(Text("Take the finite accepting runs of the controller on all members. At each common coarse history, retain each member's actual raw prefix and residual execution. A stopping node has at most one member: two different nonconflicting positive trees must have a fresh coarse divergence. At a query node, two members giving none would both have paid a nonleaf on the same coarse prefix. The common-history obstruction would force one terminal nonleaf count to be at least two, contradicting the uniform one-excess bound.")),
                Paragraph(Text("A node with at least two members therefore has a nonempty matching leaf child. Skip a query when that child is the whole survivor set, and otherwise retain its actual address and continue through that child. Finite residual execution budgets decrease, so the construction reaches a singleton. The retained list is a subsequence of the chosen member's actual residual query list. It is executed as a new route; deleted reports are never installed as observations. In particular, the original controller may pay extra nonleaves after reaching a singleton, and no original coordinate is assumed to have cost n.")),
                Paragraph(Text("For k at least three the exact coarse endpoint spectrum is empty. If a coarse Strategy had no input of cost at least n+2, integrality would give the uniform bound n+1. The first conjunct would then supply a safe endpoint route, contradicting that spectrum. Thus every such Strategy has a family member of cost at least 3k+15."))),
            DescribeRole.Theorem))));

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

    private static Formula ResultFormula()
    {
        Formula k = V("k"), pi = V("pi"), i = V("i"), z = V("z"), qs = V("qs");
        Formula indices = Call("Fin", Seq(D(2), k, Plus, D(1)));
        Formula observable = Call("CoarseObservable", Call("policy", pi));
        Formula cost = Call("C", pi, Call("F", k, i));
        Formula bridge = All("pi", V("Strategy"), Imp(observable,
            Imp(All("i", indices, Seq(cost, Sp, Le, Sp, D(3), k, Plus, D(1, 4))),
                Some("z", indices, Some("qs", Call("List", V("Address")),
                    Call("Safe", k, z, qs))))));
        Formula lower = Imp(Seq(D(3), Sp, Le, Sp, k), All("pi", V("Strategy"),
            Imp(observable, Some("i", indices,
                Seq(D(3), k, Plus, D(1, 5), Sp, Le, Sp, cost)))));
        return All("k", V("Nat"), Imp(Seq(D(1), Sp, Le, Sp, k), And(bridge, lower)));
    }
}
