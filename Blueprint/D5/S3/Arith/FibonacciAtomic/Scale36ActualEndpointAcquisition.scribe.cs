using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class Scale36ActualEndpointAcquisitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Scale36 family has distinct compatible positive trees and all literal actual endpoints.",
        H("Scale36 Actual Endpoint Acquisition"),
        Blocks(
            Paragraph(Text("For k at least one, I(k) is Unit plus Fin(k) times Fin(2). The Unit row is P0, "
                + "and the two exceptional rows in slot j are Uj and Vj. There are k active slots and one "
                + "compensation slot in the ordered right comb. E is the beta/alpha pair, A is (E,beta), "
                + "C is (A,E), B is (C,A), T is (A,C), W1 is (B,C), and KT is (T,A). P0 has C in every "
                + "active slot and KT at the tail. Uj replaces these by T and B; Vj by W1 and A. "
                + "Q(k,i) is the complete bracket-preserving preimage and n(k)=5k+11.")),
            Describe.Lean(DescribeId.Create("scale36-family-structure"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition.family_structure"),
                H("Positive, Distinct and Nonconflicting Prototypes"),
                StatementSource.FromAuthor(FamilyFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The third substitution image respects every pair in the right comb. "
                    + "Its complete preimages give positivity. The ordinary C block has five leaves; each "
                    + "exceptional block together with its compensation has sixteen. Reading a full activity "
                    + "slot recovers its tree, so the exceptional position and type determine the index. "
                    + "The activity blocks C,T,W1 and compensation blocks KT,B,A separately agree at every "
                    + "shared leaf. This agreement extends through the common ordered comb."))),
                DescribeRole.Theorem),
            Paragraph(Text("The four addresses in slot j are a=R^j LLLR, b=R^j LRR, "
                + "q=R^j LRLLR, r=R^j LLLLLR, with zero-based j. Ordinary scans ask a, then b only "
                + "after an alpha leaf. A coarse nonleaf report selects Vj at a and Uj at b. "
                + "Two alpha reports continue. A Uj target scans all other slots, then uses a,q in its "
                + "retained slot; a Vj target uses q,r. Unexpected beta reports invoke acquisition.")),
            Describe.Lean(DescribeId.Create("scale36-actual-endpoints"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition.result"),
                H("All Actual Endpoints and Exact Paid Sets"),
                StatementSource.FromAuthor(EndpointFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each route selects its actual evaluation prototype. Ordinary continuation "
                        + "requests are alpha leaves of that input. At the retained slot, the a/q and q/r "
                        + "rules distinguish P0,Uj,Vj with the displayed extra address. The paid set J equals "
                        + "the full leaf set L together with the empty or singleton set X. X is empty at "
                        + "the target itself. For a different input Uj it is b_j, except that target Vj "
                        + "uses r_j. For a different input Vj it is a_j. For input P0 and an exceptional "
                        + "target it is q at the target slot.")),
                    Paragraph(Text("The coarse completion contract compiles each finite route into an original "
                        + "Strategy whose policy depends only on the coarse chronological history. This one "
                        + "strategy is usable through both readout interfaces. A tentative selection starts full "
                        + "leaf verification; a mismatch or failed selection starts global acquisition. Strategy "
                        + "correctness and finite termination quantify over every finite source tree, from the "
                        + "same empty initial history. True cache hits preserve actual responses and the union "
                        + "of requests. The extra address is a nonleaf, so the bill is n at the target and "
                        + "n+1 at every other evaluation row."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Guard(Formula body) => Disp(All("k",V("Nat"),
        Seq(Par(Seq(D(1),Sp,Leq,Sp,V("k"))),Sp,Implies,Sp,Par(body))));
    private static Formula StructureFormula()
    {
        Formula k=V("k"), i=V("i"), j=V("j"), indices=Call("I",k), n=Call("n",k);
        Formula Tree(Formula x) => Call("F",k,x);
        return And(Call("Injective",Call("F",k)), All("i",indices,And(
            EqOf(Call("rho3",Call("Q",k,i)),Tree(i)),Call("Positive",Tree(i)),
            EqOf(Call("length",Tree(i)),n),EqOf(Call("card",Call("L",Tree(i))),n))),
            All("i",indices,All("j",indices,Call("NC",Tree(i),Tree(j)))));
    }
    private static Formula FamilyFormula() => Guard(StructureFormula());
    private static Formula EndpointFormula()
    {
        Formula k=V("k"), i=V("i"), j=V("j"), p=V("pi"), indices=Call("I",k), tree=Call("F",k,j);
        return Guard(And(StructureFormula(),EqOf(Call("card",indices),Add(Mul(D(2),k),D(1))),
            All("i",indices,Some("pi",V("Strategy"),And(
            Call("CoarseObservable",Call("policy",p)),All("j",indices,And(
                EqOf(Call("J",p,tree),Seq(Call("L",tree),Sp,Cup,Sp,Call("X",k,i,j))),
                EqOf(Call("cost",p,tree),Sub(Add(Call("n",k),D(1)),Call("indicator",EqOf(i,j)))))))))));
    }
}
