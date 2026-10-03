using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualImageAddressCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alpha leaf queries give exact positive certificates for actual Fibonacci tree images.",
        H("Exact Address Certificates for Actual Tree Images"), Blocks(
            Paragraph(Text("Sources are the existing nonempty ordered full binary trees with alpha and beta leaves. "
                + "The substitution rho sends alpha to beta and beta to (beta,alpha), and preserves pairing. "
                + "Composition c counts alpha and beta leaves. Paths are root-first Boolean lists: false is left, true is right. "
                + "Leaf labels use true for alpha and false for beta.")),
            Def("Address", "Raw addresses", "An address is a finite Boolean list, including the empty root address."),
            Def("Output", "Four endpoint results", "The endpoint result is leafAlpha, leafBeta, branch or absent."),
            Def("out", "Raw endpoint observation", "A valid path reads its original endpoint. Continuing beyond a leaf reads absent."),
            Def("height", "Maximum leaf depth", "Height is the height of the existing ordered shape decomposition. A leaf has height zero."),
            Def("ActualImage", "Actual substitution image", "ActualImage(d) is the range of the d-fold native substitution on complete source trees."),
            Def("Within", "Finite depth window", "Within(h,Q) means that each address in the finite set Q has length at most h."),
            Def("Sound", "Positive address certificate", "Sound(d,V,h,Q) means Within(h,Q) and: every complete tree U with c(U)=c(V) "
                + "and out(U,u)=out(V,u) for every u in Q belongs to ActualImage(d). There is no leaf budget on U, "
                + "no prefix-closure condition on Q, and no adaptive or random query order."),
            Def("alphaAddresses", "Alpha leaf addresses", "The finite set contains exactly the root-first addresses of alpha leaves."),
            Def("subtree", "Complete addressed subtree", "The addressed subtree is present exactly when the path reaches a node; otherwise it is absent."),
            Def("replace", "Subtree replacement", "Replacement changes the complete subtree at a valid address and retains the surrounding ordered tree. Invalid paths leave the tree unchanged."),
            Def("AlphaCovered", "Alpha coverage of branches", "Every internal node has an alpha leaf descendant, recursively throughout the tree."),
            Describe.Lean(DescribeId.Create("actual-image-address-certificate-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Sharp cardinality and depth"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("All k and h are natural numbers, V is a complete source tree, and Q is a finite set of addresses. "
                        + "I(d) denotes ActualImage(d), a(V) is the first component of c(V), D(V) is height(V), "
                        + "and S(d,V,h,Q) abbreviates Sound(d,V,h,Q), including the depth window. "
                        + "Thus below the maximum leaf depth there is no sound certificate; at or above it the minimum cardinality is exactly a(V).")),
                    Paragraph(Text("Every twice-substituted leaf block has an alpha descendant below each of its internal nodes. "
                        + "Matching all alpha endpoints forces every branch of V to remain present in a competitor. Equal total leaf and alpha counts "
                        + "then force the whole ordered tree and all its labels to agree. The alpha address set therefore attains the upper bound.")),
                    Paragraph(Text("Each alpha leaf is the right endpoint of a terminal pair (beta,alpha). Swapping either such pair to (alpha,beta) "
                        + "preserves composition and changes only its two endpoint observations. The new left alpha leaf excludes the competitor "
                        + "from the substitution image. Every sound query set must meet each endpoint pair, and these pairs are disjoint. "
                        + "A deepest pair supplies the obstruction when the path window is too shallow.")),
                    Paragraph(Text("Certificate complexity and lower bounds from disjoint sensitive blocks are classical, as in Nisan's "
                        + "CREW PRAMs and Decision Trees (1991) and Buhrman and de Wolf's Complexity Measures and Decision Tree Complexity: A Survey (2002). "
                        + "The exact cardinality for these actual substitution images with fixed composition is the tree-specific conclusion."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-image-address-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula InOf(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x,i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string x, Formula domain, Formula body) =>
        Seq(Forall, Sp, V(x), Sp, InMacro, Sp, domain, Comma, Sp, Par(body));
    private static Formula Exists(string x, Formula domain, Formula body) =>
        Seq(F.Exists, Sp, V(x), Sp, InMacro, Sp, domain, Comma, Sp, Par(body));
    private static Formula ResultFormula()
    {
        Formula k=V("k"), t=V("V"), h=V("h"), q=V("Q"), d=Seq(D(3),Sp,k);
        Formula a=Call("a",t), depth=Call("D",t), queries=Call("Finset",V("Address"));
        Formula sound=Call("S",d,t,h,q);
        Formula small=Imp(Seq(h,Sp,Lt,Sp,depth),Seq(Neg,Exists("Q",queries,sound)));
        Formula attained=Imp(LeOf(depth,h),Exists("Q",queries,And(sound,EqOf(Call("card",q),a))));
        Formula lower=All("Q",queries,Imp(sound,LeOf(a,Call("card",q))));
        return Disp(All("k",V("Nat"),Imp(LeOf(D(1),k),All("V",V("Source"),
            Imp(InOf(t,Call("I",d)),All("h",V("Nat"),And(small,attained,lower)))))));
    }
}
