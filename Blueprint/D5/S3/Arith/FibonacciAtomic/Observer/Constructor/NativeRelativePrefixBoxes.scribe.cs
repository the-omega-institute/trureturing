using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class NativeRelativePrefixBoxesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeRelativePrefixBoxes", H("Native relative prefix boxes"), Blocks(
            Paragraph(Text("Source is the original free ordered magma on Boolean leaves: true is alpha, false is beta, and substitution sends alpha to beta, beta to the ordered pair (beta,alpha), and preserves pairing. Address is List Bool with false = L and true = R. readout is the original alpha, beta, branch or absent literal reply. S d is exactly NativeConstructorArrays.S d: Canonical 0 fixes alpha, and Canonical (k+1) admits both leaves and pairs of Canonical k children. In particular S 1 contains precisely alpha, beta and C0 = (alpha,alpha).")),
            Paragraph(Text("Factor is Nat times Bool, with Boolean false and true denoting the integer second coordinates zero and one. pathCost r counts L with weight one and R with weight two. lastRight r is the last-letter R indicator for nonempty r. leafFactor r b has first coordinate pathCost r + (if b then 2 else 1); its second coordinate is b for empty r and lastRight r otherwise. Thus it is precisely (2-e,1-e) at a leaf endpoint and (s(r)+2-e,indicator last R) at a strict blocking prefix, with e(alpha)=0 and e(beta)=1.")),
            Paragraph(Text("gamma follows the actual original constructors along q. At the first actual leaf of label b it returns leafFactor of the remaining suffix and b. At a branch endpoint it returns (0,false). A blocker at index i means readout (take i q) u = leafReply b, where leafReply true = alpha and leafReply false = beta. This nonabsent leaf forces the earlier ancestors to be branches. descriptor q i b = leafFactor (drop i q) b. An absent target has a strict actual blocking prefix, rather than an absent leaf.")),
            Paragraph(Text("level d q z is the set of all u in S d with gamma q u = z. projection d q v z is the actual image of this entire level under u |-> readout v u. It is not the image of a selected representative, and repeated appearances of one literal are the same actual reply. DoubleAt q i means i+1 < length q and the letter at index i is L.")),
            Describe.Lean(DescribeId.Create("native-canonical-factor-levels"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRelativePrefixBoxes.canonical_factor_levels"),
                H("Every attained blocking factor is a relative prefix box"), WholeStatement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Classified d q z has exactly the following three alternatives. The branch factor is (0,false), its level is exactly readout q = branch, and its projection at q is the singleton branch. A singleton descriptor has some i at most length q and label b; among all valid descriptors, descriptor q j c = z holds exactly when j=i and c=b. Its level is exactly readout (take i q) = leafReply b, and that projection is the corresponding singleton.")),
                    Paragraph(Text("The double alternative has DoubleAt q i and z = descriptor q i false. Among all descriptors it consists exactly of (i,beta) and (i+1,alpha). The level is recognized by both tests: readout (take i q) belongs to {beta,branch}, and readout (take (i+1) q) belongs to {absent,alpha}. The intervening L makes take (i+1) q = take i q appended with L. These two projections of the whole level are exactly the displayed two-element sets; both alternatives are attained by actual canonical trees.")),
                    Paragraph(Text("For i<j, equality of complete descriptor factors forces b=false, c=true, j=i+1 and DoubleAt q i, and these conditions suffice. The first-coordinate gap bounds the separation of positions. At a final L the preceding beta and terminal alpha first coordinates coincide, but their second coordinates are false and true. This excludes the terminal candidate, every nonadjacent or R collision, and every class of three descriptors.")),
                    Paragraph(Text("Canonical realization uses the existing spine context with alpha at every unused sibling. Both labelled leaves are realized at every prefix, and a branch endpoint is realized by planting C0. The strict length bound permits C0 at the last represented position, while its alpha children are fixed by Canonical 0 outside the menu. These are trees of the recursive canonical carrier, not merely arbitrary trees of bounded height.")),
                    Paragraph(Text("A true second coordinate requires a first coordinate of at least two. Every initially absent target has a strict actual blocking prefix with one of the two genuine leaf labels, and its gamma is the corresponding descriptor. The theorem concerns this initial blocking formula; identification with the complete substitution trajectory is an additional assertion.")),
                    Paragraph(Text("Every member satisfies its own image conditions at every prefix, including root and q. Conversely the conditions include the one or two exact tests of its classified level. Actual tree consistency then puts the candidate in that level. For q empty there are only the two labelled leaves and a branch root, and the single tests apply. For length q = d-1 the branch realization still uses C0 and the terminal exception still applies. In particular d=1 is included.")),
                    Paragraph(Text("This is an equality relative to actual canonical trees. It gives no independent reply-array choices, additional observation service, preparation shortcut or resource bound. All coordinates refer to one actual tree."))), DescribeRole.Theorem)
        )));

    private static StatementSource WholeStatement()
    {
        var d = V("d"); var q = V("q"); var z = V("z");
        var tree = Call("S", d);
        var level = Call("level", d,q,z);
        var replies = All("v", V("Address"), Imp(Call("IsPrefix", V("v"),q),
            Member(Call("readout", V("v"),Call("val",V("u"))),Call("projection",d,q,V("v"),z))));
        var box = EqOf(level, Seq(OpenBrace,Sp,V("u"),Colon,Sp,tree,Sp,Mid,Sp,replies,Sp,CloseBrace));
        var distinct = All("i,j",V("Nat"),All("b,c",V("Bool"),
            Imp(Le(V("i"),Call("length",q)),Imp(Le(V("j"),Call("length",q)),Imp(Lt(V("i"),V("j")),
            IffOf(EqOf(Call("descriptor",q,V("i"),V("b")),Call("descriptor",q,V("j"),V("c"))),
                And(EqOf(V("b"),V("false")),And(EqOf(V("c"),V("true")),
                    And(EqOf(V("j"),Add(V("i"),D(1))),Call("DoubleAt",q,V("i")))))))))));
        var leaves = All("i",V("Nat"),Imp(Le(V("i"),Call("length",q)),All("b",V("Bool"),
            Ex("u",tree,EqOf(Call("readout",Call("take",V("i"),q),Call("val",V("u"))),Call("leafReply",V("b")))))));
        var branch = Ex("u",tree,EqOf(Call("readout",q,Call("val",V("u"))),V("branch")));
        var attained = Ex("u",tree,EqOf(Call("gamma",q,Call("val",V("u"))),z));
        var guard = All("u",V("Source"),Imp(EqOf(Call("snd",Call("gamma",q,V("u"))),V("true")),
            Le(D(2),Call("fst",Call("gamma",q,V("u"))))));
        var blocked = All("u",V("Source"),Imp(EqOf(Call("readout",q,V("u")),V("absent")),
            Ex("i",V("Nat"),And(Lt(V("i"),Call("length",q)),Ex("b",V("Bool"),
                And(EqOf(Call("readout",Call("take",V("i"),q),V("u")),Call("leafReply",V("b"))),
                    EqOf(Call("gamma",q,V("u")),Call("descriptor",q,V("i"),V("b")))))))));
        var conclusion = And(box,And(Call("Classified",d,q,z),And(distinct,
            And(leaves,And(branch,And(guard,blocked))))));
        var factors = All("z",V("Factor"),Imp(attained,conclusion));
        var words = All("q",V("Address"),Imp(Lt(Call("length",q),d),factors));
        return StatementSource.FromAuthor(Disp(All("d",V("Nat"),words)));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..xs]);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall,Sp,Seq(n.Split(',').Select((name,i) => i==0 ? V(name) : Seq(Comma,Sp,V(name))).ToArray()),Colon,Sp,t,Comma,Sp,Open,b,Close);
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Open,b,Close);
    private static Formula And(Formula a, Formula b) => Seq(Open,a,Close,Sp,Land,Sp,Open,b,Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open,a,Close,Sp,Implies,Sp,Open,b,Close);
    private static Formula IffOf(Formula a, Formula b) => Seq(Open,a,Close,Sp,Iff,Sp,Open,b,Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula Lt(Formula a, Formula b) => Seq(a,Sp,F.Lt,Sp,b);
    private static Formula Le(Formula a, Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula Add(Formula a, Formula b) => Seq(a,Sp,Plus,Sp,b);
    private static Formula Member(Formula a, Formula b) => Seq(a,Sp,InMacro,Sp,b);
}
