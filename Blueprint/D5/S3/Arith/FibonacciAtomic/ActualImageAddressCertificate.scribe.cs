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
                + "Composition c counts alpha and beta leaves. Paths reuse the frozen ActualTreeReadoutAcquisition.Address type of finite Boolean lists, including the empty root address. "
                + "Endpoint observations use its Reply and address-first readout; complete leaf sets use ActualImageSevenLeafSeparation.leafAddresses. "
                + "Leaf labels use true for alpha and false for beta. Alpha endpoints reuse ActualLeafHistoryRigidity.alphaLeaves, and addressed subtrees reuse its subtree with the address supplied first.")),
            Def("height", "Maximum leaf depth", "Height is the height of the existing ordered shape decomposition. A leaf has height zero."),
            Def("ActualImage", "Actual substitution image", "ActualImage(d) is the range of the d-fold native substitution on complete source trees."),
            Def("Within", "Finite depth window", "Within(h,Q) means that each address in the finite set Q has length at most h."),
            Def("Sound", "Positive address certificate", "Sound(d,V,h,Q) means Within(h,Q) and: every complete tree U with c(U)=c(V) "
                + "and readout(u,U)=readout(u,V) for every u in Q belongs to ActualImage(d). Exact composition is the only competitor promise, "
                + "no prefix-closure condition on Q, and no adaptive or random query order."),
            Def("UnSound", "Certificates without a composition promise", "Every complete source U matching all queried endpoint results must belong to ActualImage(d). No composition or leaf-count constraint is placed on U; the depth window is imposed separately."),
            Def("replace", "Subtree replacement", "Replacement changes the complete subtree at a valid address and retains the surrounding ordered tree. Invalid paths leave the tree unchanged."),
            Def("AlphaCovered", "Alpha coverage of branches", "Every internal node has an alpha leaf descendant, recursively throughout the tree."),
            Def("rightComb", "Right comb source", "The zero comb is beta. The successor comb pairs alpha on the left with the preceding comb on the right, giving m alpha side leaves and one terminal beta at m right steps."),
            Helper("image_positive", "Third-image inclusion", "For every natural d at least three and every U in I(d), U is a third substitution image."),
            Helper("positive", "Positive leaf total", "Every nonempty source has strictly positive sum of alpha and beta composition counts."),
            Helper("alpha_card", "Alpha cardinality", "For every complete source t, the cardinality of alphaLeaves(t) equals the alpha component of composition(t)."),
            Helper("leaf_data", "Leaf depth and beta cardinality", "For every source t, all its leaf addresses have length at most height(t), and its beta-filtered leaf set has cardinality equal to the beta composition component."),
            Helper("structural", "Twice-substituted structure", "For every source t, rho squared(t) is AlphaCovered; each alpha leaf is the right child of a terminal pair(beta,alpha), and some alpha leaf reaches maximum height."),
            Helper("no_left_alpha", "Left alpha obstruction", "For every third image t and every address r, a subtree alpha at r followed by a left step is impossible."),
            Helper("leaf_change", "Changing a leaf label", "Replacing the leaf b at address s by c retains a leaf c there, adds composition(c) while removing composition(b), and preserves every readout away from s."),
            Helper("no_beta_cherry", "Double beta obstruction", "A third image cannot have beta replies at both immediate children of a single address."),
            Helper("image_structure", "Image alpha structure", "For every k at least one and every U in I(3k), U is AlphaCovered and each alpha address is the right child of a terminal pair(beta,alpha)."),
            Helper("beta_surplus", "Strict beta surplus", "For every k at least one and every V in I(3k), the beta composition count is strictly larger than its alpha count."),
            Helper("exchange_composition", "Exchange composition", "For every source V and two addresses s,t, the two leaf-change composition equations for alpha to beta at s and beta to alpha at t imply that the resulting composition equals composition(V)."),
            Helper("exchange_conflict", "Exchange obstruction", "Let V,Wone,W be sources, s and t distinct addresses and s the right child of r. Suppose the subtree at r in V is pair(beta,alpha), t has beta reply in V, s is beta in Wone, t is alpha in W, Wone matches V away from s, and W matches Wone away from t. Then W cannot be a third image."),
            Describe.Lean(DescribeId.Create("actual-image-alpha-mul"),
                DeclarationHandle.Create(Prefix + "alpha_mul"), H("Alpha addresses of a pair"),
                StatementSource.FromAuthor(AlphaMulFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The alpha address set of pair(s,t) is the union of the left-prefixed alpha addresses of s "
                        + "and the right-prefixed alpha addresses of t. The two prefixes are disjoint."))), DescribeRole.Theorem),
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
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-image-address-certificate-rigidity"),
                DeclarationHandle.Create(Prefix + "rigidity"), H("Unique optimal certificates and the complete leaf frontier"),
                StatementSource.FromAuthor(RigidityFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For k at least one, V belongs to I(3 times k). Write A(V) for its alpha addresses, "
                        + "L(V) for all its leaf addresses, a(V) for its alpha count and n(V) for its total leaf count. "
                        + "W(h,Q) means Within(h,Q), and U(d,V,Q) means UnSound(d,V,Q). "
                        + "At or above D(V), the complete leaf frontier is the unique minimum certificate without a composition promise.")),
                    Paragraph(Text("Three substitution steps give strictly more beta leaves than alpha leaves. If a sound set of a(V) queries "
                        + "omits an alpha leaf, it also omits a beta leaf. Exchanging those labels preserves composition and all queried results. "
                        + "If the chosen beta is the alpha leaf's left sibling, the exchange puts an alpha on the left. Otherwise the old "
                        + "terminal pair becomes (beta,beta). Both possibilities violate the structure of a twice-substituted tree.")),
                    Paragraph(Text("Without a composition promise, omitting any leaf permits the frozen flip operation. The source_foundation theorem "
                        + "excludes that flipped tree from the third image and supplies unchanged readouts at every other address. "
                        + "Every image at depth 3k is a third image. Conversely, the same frozen theorem reconstructs a complete "
                        + "ordered tree from its labeled leaf frontier.")),
                    Paragraph(Text("The shallow-window obstruction follows from the fixed-composition certificate theorem. At or above that depth, "
                        + "all n(V) leaves are available, and the complete-leaf condition gives both the lower bound and uniqueness. "
                        + "The exact uniqueness and complete-leaf equivalence are specific to these substitution images; general "
                        + "decision-tree certificate complexity supplies neighboring background."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-image-address-height-frontier"),
                DeclarationHandle.Create(Prefix + "heightFrontier"), H("Sharp leaf budget above a height"),
                StatementSource.FromAuthor(FrontierFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For natural k at least one put d=3k, A=rho iterated d times on alpha and B=rho iterated d times on beta. "
                        + "F denotes the Fibonacci sequence with F(0)=0 and F(1)=1. Write a=F(d+1), b=F(d+2), and n(X) for the total number of leaves. "
                        + "The height D counts edges. The budget C(d,h) is a when h is at most d-2, "
                        + "and b plus a times m otherwise, where m=h+1-d uses natural truncated subtraction. "
                        + "Thus at h=d-1 the value of m is zero.")),
                    Paragraph(Text("Let U(0)=beta and U(m+1)=(alpha,U(m)). Define V(d,h)=A in the low range "
                        + "and rho iterated d times on U(m) in the high range. Define r(d,h) as d-2 left steps "
                        + "in the low range and m right steps followed by d-1 left steps in the high range. "
                        + "The subtree at r is J=(beta,alpha). Let W(d,h) replace that subtree by (alpha,beta). "
                        + "In the formula c is composition, I is the actual image, sub is the addressed subtree, "
                        + "some is the present-subtree constructor and R(m) is the address of m right steps.")),
                    Paragraph(Text("Each source leaf becomes one A or B block. Every sibling subtree along a source path "
                        + "contains at least a output leaves. Induction on the source gives a lower bound a for every image "
                        + "and b plus a times (D-d) whenever its height D is at least d. "
                        + "The strict relation b<2a handles a deepest alpha block as well as a deepest beta block. "
                        + "The right comb attains the high bound, with its beta block at R(m).")),
                    Paragraph(Text("Swapping the specified terminal pair preserves exact composition and changes only the "
                        + "two leaf labels at depths above h. Every endpoint observation within the window therefore agrees, "
                        + "including branches and absent endpoints. The left alpha leaf excludes W from the actual image. "
                        + "The universal lower bound together with the explicit attaining image characterizes the minimum "
                        + "leaf budget over images whose height exceeds h."))), DescribeRole.Theorem))));

    private static DocumentBlock Helper(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-image-address-helper-" + name.Replace("_", "-")), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

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
    private static Formula AlphaMulFormula()
    {
        Formula s=V("s"),t=V("t");
        return Disp(All("s",V("Source"),All("t",V("Source"),EqOf(
            Call("alphaLeaves",Call("pair",s,t)),Call("union",
                Call("prefixLeft",Call("alphaLeaves",s)),Call("prefixRight",Call("alphaLeaves",t)))))));
    }
    private static Formula ResultFormula()
    {
        Formula k=V("k"), t=V("V"), h=V("h"), q=V("Q"), d=Seq(D(3),Sp,Cdot,Sp,k);
        Formula a=Call("a",t), depth=Call("D",t), queries=Call("Finset",V("Address"));
        Formula sound=Call("S",d,t,h,q);
        Formula small=Imp(Seq(h,Sp,Lt,Sp,depth),Seq(Neg,Exists("R",queries,Call("S",d,t,h,V("R")))));
        Formula attained=Imp(LeOf(depth,h),Exists("R",queries,And(Call("S",d,t,h,V("R")),EqOf(Call("card",V("R")),a))));
        Formula lower=All("Q",queries,Imp(sound,LeOf(a,Call("card",q))));
        return Disp(All("k",V("Nat"),Imp(LeOf(D(1),k),All("V",V("Source"),
            Imp(InOf(t,Call("I",d)),All("h",V("Nat"),And(small,attained,lower)))))));
    }
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Leftrightarrow,Sp,Par(b));
    private static Formula RigidityFormula()
    {
        Formula k=V("k"), t=V("V"), h=V("h"), q=V("Q"), d=Seq(D(3),Sp,Cdot,Sp,k);
        Formula a=Call("a",t), n=Call("n",t), depth=Call("D",t);
        Formula alpha=Call("A",t), leaves=Call("L",t), queries=Call("Finset",V("Address"));
        Formula within=Call("W",h,q), sound=Call("S",d,t,h,q), un=Call("U",d,t,q);
        Formula unique=All("h",V("Nat"),Imp(LeOf(depth,h),All("Q",queries,
            Imp(within,IffOf(And(sound,EqOf(Call("card",q),a)),EqOf(q,alpha))))));
        Formula full=All("h",V("Nat"),All("Q",queries,
            Imp(within,IffOf(un,Seq(leaves,Sp,Subseteq,Sp,q)))));
        Formula shallow=All("h",V("Nat"),Imp(Seq(h,Sp,Lt,Sp,depth),Seq(Neg,
            Exists("R",queries,And(Call("W",h,V("R")),Call("U",d,t,V("R")))))));
        Formula bounds=All("Q",queries,Imp(within,Imp(un,And(LeOf(n,Call("card",q)),
            IffOf(EqOf(Call("card",q),n),EqOf(q,leaves))))));
        Formula attained=All("h",V("Nat"),Imp(LeOf(depth,h),And(Call("W",h,leaves),
            Call("U",d,t,leaves),EqOf(Call("card",leaves),n),bounds)));
        return Disp(All("k",V("Nat"),Imp(LeOf(D(1),k),All("V",V("Source"),
            Imp(InOf(t,Call("I",d)),And(unique,full,shallow,attained))))));
    }

    private static Formula FrontierFormula()
    {
        Formula k=V("k"), h=V("h"), d=Seq(D(3),Sp,Cdot,Sp,k);
        Formula a=Call("F",Seq(d,Sp,Plus,Sp,D(1))), b=Call("F",Seq(d,Sp,Plus,Sp,D(2)));
        Formula prev=Call("F",Seq(d,Sp,Minus,Sp,D(1))), curr=Call("F",d);
        Formula m=Call("m",d,h), budget=Call("C",d,h), t=Call("V",d,h), w=Call("W",d,h);
        Formula alpha=Call("A",d), beta=Call("B",d), r=Call("r",d,h);
        Formula pair(Formula x, Formula y) => Seq(Open,x,Comma,Sp,y,Close);
        Formula blocks=And(EqOf(Call("D",alpha),Seq(d,Sp,Minus,Sp,D(1))),
            EqOf(Call("D",beta),d),EqOf(Call("c",alpha),pair(prev,curr)),
            EqOf(Call("c",beta),pair(curr,a)),EqOf(Call("n",alpha),a),EqOf(Call("n",beta),b),
            EqOf(b,Seq(a,Sp,Plus,Sp,curr)),Seq(b,Sp,Lt,Sp,D(2),Sp,Cdot,Sp,a));
        Formula lower=All("X",V("Source"),Imp(InOf(V("X"),Call("I",d)),
            Imp(Seq(h,Sp,Lt,Sp,Call("D",V("X"))),LeOf(budget,Call("n",V("X"))))));
        Formula observe=All("u",V("Address"),Imp(LeOf(Call("length",V("u")),h),
            EqOf(Call("readout",V("u"),w),Call("readout",V("u"),t))));
        Formula high=Imp(LeOf(Seq(d,Sp,Minus,Sp,D(1)),h),And(
            EqOf(Call("c",t),pair(Seq(prev,Sp,Cdot,Sp,m,Sp,Plus,Sp,curr),
                Seq(curr,Sp,Cdot,Sp,m,Sp,Plus,Sp,a))),
            EqOf(Call("sub",t,Call("R",m)),Call("some",beta))));
        return Disp(All("k",V("Nat"),Imp(LeOf(D(1),k),All("h",V("Nat"),And(blocks,lower,
            InOf(t,Call("I",d)),Seq(h,Sp,Lt,Sp,Call("D",t)),EqOf(Call("sub",t,r),Call("some",V("J"))),
            Seq(Neg,Sp,Par(InOf(w,Call("I",d)))),EqOf(Call("c",w),Call("c",t)),observe,
            EqOf(Call("n",t),budget),high)))));
    }

}
