using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class QuantityAddressCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/QuantityAddressCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact quantity and raw addresses determine the sharp positive certificate frontier.",
        H("Quantity Address Certificates"), Blocks(
            Paragraph(Text("Sources are the existing nonempty finite ordered full binary trees. "
                + "The native substitution rho sends alpha to beta and beta to pair(beta,alpha), preserving ordered pairing. "
                + "A(V) and B(V) are the original alpha and beta leaf-address sets; a(V) and b(V) are their cardinalities. "
                + "The scalar m(V)=2a(V)+3b(V) uses GraftAffineClosure.quantity on the existing composition. "
                + "I(d) is the range of rho iterated d times. D(V) is maximum leaf depth, with root depth zero. "
                + "Addresses and all four raw replies reuse ActualTreeReadoutAcquisition. LL, LR and R denote "
                + "the Boolean lists [false,false], [false,true] and [true]. Pairset(x,y) denotes their unordered two-element set.")),
            Describe.Lean(DescribeId.Create("quantity-address-sound"), DeclarationHandle.Create(Prefix + "QuantitySound"),
                H("Quantity soundness"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("S(d,V,h,Q) means that every address in the finite set Q has length at most h, "
                        + "and every complete source U with m(U)=m(V) and matching raw replies at all addresses in Q lies in I(d). "
                        + "Competitors have only this exact scalar promise; their composition, number of leaves, shape and height are unrestricted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantity-address-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Sharp frontier and all minimum sets"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every natural k at least one, every V in I(3k) and every natural depth h, a(V) is positive. "
                        + "Below D(V) no quantity-sound query set exists. At or above D(V), when a(V) is at least two, "
                        + "the set B(V) is sound, all sound sets have at least b(V) addresses, and equality holds exactly for B(V).")),
                    Paragraph(Text("If a(V)=1 then 3k=3 and V=rho cubed(alpha)=pair(pair(beta,alpha),beta), with two beta leaves. "
                        + "At or above its height all sound sets have at least two addresses. Exactly Pairset(LL,LR), Pairset(LL,R) "
                        + "and Pairset(LR,R) attain this bound, and each is sound.")),
                    Paragraph(Text("Matching every beta leaf preserves the full branch skeleton. Any remaining alpha slot contains a nonempty subtree "
                        + "of quantity at least two, with equality only for alpha. Additivity and equality of total quantity force equality in every slot, "
                        + "so the complete competitor tree equals V.")),
                    Paragraph(Text("Exchanging an omitted alpha and an omitted beta preserves quantity and excludes the resulting tree from the image. "
                        + "Thus a sound set contains every alpha or every beta address. If two beta addresses are omitted, replace one beta by alpha "
                        + "and the other by pair(alpha,alpha). The joint modification preserves quantity and changes replies only at the two beta addresses "
                        + "and the two immediate children of the expanded slot. Soundness forces a queried immediate child for each omitted beta. "
                        + "Those children are distinct and outside the original leaf set, giving the sharp cardinality bound.")),
                    Paragraph(Text("The single-alpha case reduces to the unique single-alpha third image. The two mixed pairs fix two leaf slots "
                        + "and leave quantity three for the remaining slot, whose only nonempty realization is beta. "
                        + "The shallow-depth obstruction is the existing composition-preserving terminal-pair swap."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Leftrightarrow, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x,i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula Or(params Formula[] xs) => Seq(xs.Select((x,i) =>
        i == 0 ? Par(x) : Seq(Sp, Lor, Sp, Par(x))).ToArray());
    private static Formula All(string x, Formula domain, Formula body) =>
        Seq(Forall, Sp, V(x), Sp, InMacro, Sp, domain, Comma, Sp, Par(body));
    private static Formula Triple(Formula q) => Or(
        EqOf(q, Call("Pairset", V("LL"), V("LR"))),
        EqOf(q, Call("Pairset", V("LL"), V("R"))),
        EqOf(q, Call("Pairset", V("LR"), V("R"))));
    private static Formula ResultFormula()
    {
        Formula k=V("k"), t=V("V"), h=V("h"), q=V("Q"), d=Seq(D(3),Sp,Cdot,Sp,k);
        Formula a=Call("a",t), b=Call("b",t), beta=Call("B",t), depth=Call("D",t);
        Formula queries=Call("Finset",V("Address")), sound=Call("S",d,t,h,q);
        Formula shallow=Imp(Seq(h,Sp,Lt,Sp,depth),Seq(Neg,Sp,
            F.Exists,Sp,V("Q"),Sp,InMacro,Sp,queries,Comma,Sp,Par(sound)));
        Formula general=Imp(LeOf(depth,h),Imp(LeOf(D(2),a),And(Call("S",d,t,h,beta),
            All("Q",queries,Imp(sound,And(LeOf(b,Call("card",q)),
                IffOf(EqOf(Call("card",q),b),EqOf(q,beta))))))));
        Formula small=Imp(EqOf(a,D(1)),And(EqOf(d,D(3)),EqOf(t,Call("rhoCubed",V("alpha"))),
            EqOf(b,D(2)),Imp(LeOf(depth,h),And(
                All("Q",queries,Imp(sound,And(LeOf(D(2),Call("card",q)),
                    IffOf(EqOf(Call("card",q),D(2)),Triple(q))))),
                All("Q",queries,Imp(Triple(q),sound))))));
        return Disp(All("k",V("Nat"),Imp(LeOf(D(1),k),All("V",V("Source"),
            Imp(Seq(t,Sp,InMacro,Sp,Call("I",d)),All("h",V("Nat"),
                And(LeOf(D(1),a),shallow,general,small)))))));
    }
}
