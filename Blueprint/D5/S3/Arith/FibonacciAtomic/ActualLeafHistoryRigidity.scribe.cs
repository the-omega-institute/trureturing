using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualLeafHistoryRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual third Fibonacci images admit complete node classification, five-row leaf forcing, and literal frontier recovery.",
        H("Native Leaf-History Geometry and Literal Context Recovery"),
        Blocks(
            Paragraph(Text("T is FreeMagma Bool: nonempty finite ordered full binary trees with true labelled alpha "
                + "and false labelled beta. The original substitution sends alpha to beta, beta to pair(beta,alpha), "
                + "and preserves ordered pairs. R is its actual third iterate. Positive(P) means P=R(Q) for some Q in T. "
                + "Word is List Bool, with false left, true right and the empty root included. read(u,P) is the "
                + "native four-valued reply alpha, beta, branch or absent, and Leaves(P) enumerates actual leaf words. "
                + "E=pair(beta,alpha), A=pair(E,beta), C=pair(A,E). n is native leaf count.")),
            Def("LeafHistory", "Arbitrary finite histories", "History is a finite list of pairs (word,reply). "
                + "Repeated requests and all four reply types are allowed."),
            Def("Compatible", "Positive leaf-only comparison", "compatible(H,P) means Positive(P) and, for each "
                + "(u,y) in H with y equal to alpha or beta, read(u,P)=y. Branch and absent pairs impose no constraint."),
            Def("BlockKind", "The two literal block kinds", "Kind has exactly a and c."),
            Def("BlockKind.tree", "Literal block interpretation", "tree(a)=A and tree(c)=C. A block d is a pair "
                + "(root(d),kind(d)) in Word times Kind."),
            Def("decodeBlock", "The exact five-row leaf decoder", "decode(wR,beta)=some(w,a); "
                + "decode(wLL,beta)=some(w,a); decode(wLR,alpha)=some(w,a); "
                + "decode(wRL,beta)=some(w,c); decode(wRR,alpha)=some(w,c). All other pairs decode to none. "
                + "The decoder examines the reversed address, so the beta R row also includes depth-one reports."),
            Def("forcedBlocks", "History blocks as a finite set", "blocks(H) is the finite-set view of filterMap(decode,H). "
                + "Repeated blocks are retained once. Only leaf replies have nonempty decoded values."),
            Def("alphaLeaves", "Actual alpha addresses", "alpha(P) filters the actual finite leaf-address set by read(u,P)=alpha."),
            Def("gamma", "Covered alpha union", "gamma(H) is the union over d in blocks(H) of root(d) prefixed "
                + "alpha addresses of tree(kind(d)). For a it contributes root(d)LR, and for c it contributes "
                + "root(d)LLR and root(d)RR. This is a set union; overlapping contributions count once."),
            Def("uncovered", "Reference residual", "unc(H,P)=alpha(P) minus gamma(H)."),
            Def("OutputContext", "Finite ordered literal output contexts", "Context has constructors hole, left(J,R), "
                + "and right(L,J), where L and R are actual native output trees."),
            Def("OutputContext.plug", "Literal hole filling", "plug(hole,X)=X; plug(left(J,R),X)=pair(plug(J,X),R); "
                + "plug(right(L,J),X)=pair(L,plug(J,X))."),
            Def("OutputContext.holeAddress", "Actual hole word", "hole(hole) is empty; hole(left(J,R))=L hole(J); "
                + "hole(right(L,J))=R hole(J)."),
            Def("OutputContext.outsideLeaves", "Literal outside leaf count", "outside(hole)=0; "
                + "outside(left(J,R))=outside(J)+n(R); outside(right(L,J))=n(L)+outside(J)."),
            Def("subtree", "Actual subtree navigation", "sub(empty,P)=some(P); crossing an atomic leaf at a "
                + "nonempty word gives none; L and R choose the corresponding ordered child."),
            Def("BlockOffset", "Complete canonical block offset table", "offset(true,z,Y) lists precisely "
                + "(empty,A),(L,E),(LL,beta),(LR,alpha),(R,beta). offset(false,z,Y) lists precisely "
                + "(empty,C),(L,A),(LL,E),(LLL,beta),(LLR,alpha),(LR,beta),(R,E),(RL,beta),(RR,alpha)."),
            Def("ImagePosition", "Preimage branch or canonical leaf block", "position(Q,u,Y) means either "
                + "sub(u,Q)=some(pair(q,r)) and Y=pair(R(q),R(r)), or there are v,b,z with "
                + "sub(v,Q)=some(atom(b)), u=v concat z, and offset(b,z,Y)."),
            Paragraph(Text("concat is ordered word concatenation; prefix is ordinary word prefix. "
                + "some and none are Option constructors, atom(b) is the native labelled leaf, "
                + "reply(true)=alpha and reply(false)=beta. nav(z) is the function Y mapped to sub(z,Y), "
                + "and bind is Option.bind. The theorem's read cases are separated into none and some "
                + "conditions below. All displayed quantifiers range over the native objects just defined.")),
            Describe.Lean(DescribeId.Create("actual-leaf-history-geometry"),
                DeclarationHandle.Create(Prefix + "actual_address_geometry"), H("Complete Address and History Geometry"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Induction on the original preimage locates every existing output subtree. "
                        + "A preimage branch keeps its two actual positive children. A preimage leaf gives A or C, "
                        + "whose complete finite offset tables account for all remaining nodes. Positive children "
                        + "have at least three leaves, so a composite branch has at least six. The table then "
                        + "makes E the unique two-leaf subtree and A the unique three-leaf subtree of a positive ambient tree.")),
                    Paragraph(Text("The five report suffixes cover every compatible positive leaf. A beta right "
                        + "child determines A. Beta left children and alpha right children belong to E; the "
                        + "side of E in its parent chooses A or C. The finite table includes root block queries, "
                        + "all short leaf addresses, and A inside the immediate left side of C. Determinism of "
                        + "the suffix decoder gives uniqueness. Each retained history block occurs in every "
                        + "compatible tree, hence every covered alpha is an actual alpha there.")),
                    Paragraph(Text("Comparable A/C roots can only be equal or be a C with its immediate left A. "
                        + "All other block roots are incomparable. If no alpha remains uncovered, the LR alpha "
                        + "of each canonical A or the RR alpha of each canonical C fixes that entire block in "
                        + "every competitor. Their union is the reference tree's complete labelled frontier; "
                        + "the existing complete-frontier theorem then identifies the literal outputs without comparing sizes.")),
                    Paragraph(Text("A nonexistent subtree word is exactly a strict extension of a leaf. "
                        + "Two actual leaf words related by prefix coincide and have the same label. "
                        + "Given a reference subtree at h and matching labelled leaves outside h, induction "
                        + "along h constructs a literal output context. Each sibling's full frontier forces "
                        + "the competitor to have the same sibling and a branch at the path prefix. Thus the "
                        + "hole exists in every matching arbitrary tree. An empty h gives the single root hole.")),
                    Paragraph(Text("The explicit gamma union gives its exact LR and LLR/RR membership forms. "
                        + "Suffix cancellation shows that covered RR forces that same C block; covered LR "
                        + "forces that A or an immediately enclosing C. For a singleton residual x, classify "
                        + "the canonical block containing x. A missing C-left alpha would leave C-right covered, "
                        + "forcing C and covering x, a contradiction. Therefore the only cases are an A alpha "
                        + "or a C-right alpha. In the latter case the left alpha is covered and fixes the left A "
                        + "in all competitors, without a size premise. Native navigation transfers all four "
                        + "readout values through an existing subtree and transfers subtree lookup by Option.bind."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) =>
        name.Contains(".", StringComparison.Ordinal) ? Paragraph(Text(prose)) : Describe.Lean(
        DescribeId.Create("leaf-history-" + name.Replace(".", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula InOf(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula NegOf(Formula a) => Seq(Neg, Sp, Par(a));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula OrOf(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Lor, Sp, Par(x))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula Word(params Formula[] bits) => Seq(OpenBracket,
        Seq(bits.Select((x, i) => i == 0 ? x : Seq(Comma, Sp, x)).ToArray()), CloseBracket);

    private static Formula ResultFormula()
    {
        Formula t = V("T"), word = Call("Word"), boolean = Call("Bool"), history = Call("History");
        Formula block = Call("Block"), context = Call("Context"), reply = Call("Reply");
        Formula p = V("P"), pp = V("Pp"), q = V("Q"), u = V("u"), v = V("v"), w = V("w");
        Formula z = V("z"), y = V("Y"), b = V("b"), c = V("c"), d = V("d"), h = V("h"), hst = V("H");
        Formula s = V("S"), tt = V("Z"), x = V("X"), j = V("J"), r = V("r"), lp = V("L"), rr = V("Rr");
        Formula l = V("L"), right = V("R"), a = V("A"), ec = V("E"), cc = V("C");
        Formula none = Call("none"), alpha = Call("alpha"), beta = Call("beta");
        Formula Cat(Formula aa, Formula bb) => Call("concat", aa, bb);
        Formula Sub(Formula aa, Formula tree) => Call("sub", aa, tree);
        Formula SomeOf(Formula tree) => Call("some", tree);
        Formula Read(Formula aa, Formula tree) => Call("read", aa, tree);
        Formula Positive(Formula tree) => Call("Positive", tree);
        Formula Compat(Formula tree) => Call("compatible", hst, tree);
        Formula Gamma = Call("gamma", hst);
        Formula Blocks = Call("blocks", hst);
        Formula Unc = Call("unc", hst, p);
        Formula Prefix(Formula aa, Formula bb) => Call("prefix", aa, bb);
        Formula IsBlock(Formula tree) => OrOf(EqOf(tree, a), EqOf(tree, cc));
        Formula LR(Formula aa) => Cat(aa, Word(l, right));
        Formula RR(Formula aa) => Cat(aa, Word(right, right));
        Formula LLR(Formula aa) => Cat(aa, Word(l, l, right));
        Formula classification = All("Q", t, All("u", word, All("Y", t,
            IffOf(EqOf(Sub(u, Call("R", q)), SomeOf(y)), Call("position", q, u, y)))));
        Formula small = All("P", t, Imp(Positive(p), All("u", word, All("Y", t,
            Imp(EqOf(Sub(u, p), SomeOf(y)), And(Imp(EqOf(Call("n", y), D(2)), EqOf(y, ec)),
                Imp(EqOf(Call("n", y), D(3)), EqOf(y, a))))))));
        Formula Row(Formula tail, Formula response, Formula tree) =>
            Imp(EqOf(Read(Cat(w, tail), p), response), EqOf(Sub(w, p), SomeOf(tree)));
        Formula rows = All("P", t, Imp(Positive(p), All("w", word, And(
            Row(Word(right), beta, a), Row(Word(l, l), beta, a), Row(Word(l, right), alpha, a),
            Row(Word(right, l), beta, cc), Row(Word(right, right), alpha, cc)))));
        Formula Decode(Formula item) => And(EqOf(Call("decode", u, r), SomeOf(item)),
            EqOf(Sub(Call("root", item), p), SomeOf(Call("tree", Call("kind", item)))));
        Formula unique = All("P", t, Imp(Positive(p), All("u", word, All("r", reply,
            Imp(And(OrOf(EqOf(r, alpha), EqOf(r, beta)), EqOf(Read(u, p), r)),
                Some("d", block, And(Decode(d), All("q", block, Imp(Decode(V("q")), EqOf(V("q"), d))))))))));
        Formula historyBlocks = All("H", history, All("P", t, Imp(Compat(p), And(
            All("d", block, Imp(InOf(d, Blocks), EqOf(Sub(Call("root", d), p), SomeOf(Call("tree", Call("kind", d)))))),
            Call("subset", Gamma, Call("alpha", p))))));
        Formula overlap = All("P", t, All("u", word, All("v", word, All("S", t, All("Z", t,
            Imp(And(IsBlock(s), IsBlock(tt), EqOf(Sub(u, p), SomeOf(s)), EqOf(Sub(v, p), SomeOf(tt))),
                OrOf(And(EqOf(u, v), EqOf(s, tt)), And(NegOf(Prefix(u, v)), NegOf(Prefix(v, u))),
                    And(EqOf(s, cc), EqOf(tt, a), EqOf(v, Cat(u, Word(l)))),
                    And(EqOf(s, a), EqOf(tt, cc), EqOf(u, Cat(v, Word(l)))))))))));
        Formula zero = All("H", history, All("P", t, Imp(Compat(p), Imp(EqOf(Call("card", Unc), D(0)),
            All("Pp", t, Imp(Compat(pp), EqOf(pp, p)))))));
        Formula absent = All("P", t, All("u", word, IffOf(EqOf(Sub(u, p), none),
            Some("v", word, Some("b", boolean, Some("z", word, And(
                EqOf(Sub(v, p), SomeOf(Call("atom", b))), EqOf(u, Cat(v, z)), NeOf(z, Word()))))))));
        Formula leafPrefix = All("P", t, All("u", word, All("v", word, All("b", boolean, All("c", boolean,
            Imp(And(EqOf(Sub(u, p), SomeOf(Call("atom", b))), EqOf(Sub(v, p), SomeOf(Call("atom", c))),
                Prefix(u, v)), And(EqOf(u, v), EqOf(b, c))))))));
        Formula outside = All("u", word, Imp(And(InOf(u, Call("Leaves", p)), NegOf(Prefix(h, u))),
            EqOf(Read(u, pp), Read(u, p))));
        Formula contexts = All("h", word, All("P", t, All("X", t, Imp(EqOf(Sub(h, p), SomeOf(x)),
            Some("J", context, And(EqOf(Call("hole", j), h), EqOf(Call("plug", j, x), p),
                All("Pp", t, Imp(outside, Some("Y", t, And(EqOf(Sub(h, pp), SomeOf(y)),
                    EqOf(Call("plug", j, y), pp)))))))))));
        Formula gammaA = Some("w", word, And(InOf(Pair(w, Call("a")), Blocks), EqOf(u, LR(w))));
        Formula gammaC = Some("w", word, And(InOf(Pair(w, Call("c")), Blocks), OrOf(EqOf(u, LLR(w)), EqOf(u, RR(w)))));
        Formula gammaShape = All("H", history, All("u", word, IffOf(InOf(u, Gamma), OrOf(gammaA, gammaC))));
        Formula gammaBlocks = All("H", history, All("w", word, And(
            Imp(InOf(RR(w), Gamma), InOf(Pair(w, Call("c")), Blocks)),
            Imp(InOf(LR(w), Gamma), OrOf(InOf(Pair(w, Call("a")), Blocks),
                Some("v", word, And(EqOf(w, Cat(v, Word(l))), InOf(Pair(v, Call("c")), Blocks))))))));
        Formula xpos = V("x");
        Formula singleton = All("H", history, All("P", t, Imp(Compat(p), Imp(EqOf(Call("card", Unc), D(1)),
            Some("x", word, And(EqOf(Unc, Seq(OpenBrace, xpos, CloseBrace)), OrOf(
                Some("v", word, And(EqOf(Sub(v, p), SomeOf(a)), EqOf(xpos, LR(v)))),
                Some("v", word, And(EqOf(Sub(v, p), SomeOf(cc)), EqOf(xpos, RR(v)), InOf(LLR(v), Gamma),
                    All("Pp", t, Imp(Compat(pp), EqOf(Sub(Cat(v, Word(l)), pp), SomeOf(a)))))))))))));
        Formula readNone = All("v", word, All("z", word, All("P", t, Imp(EqOf(Sub(v, p), none),
            EqOf(Read(Cat(v, z), p), Call("absent"))))));
        Formula readSome = All("v", word, All("z", word, All("P", t, All("Y", t,
            Imp(EqOf(Sub(v, p), SomeOf(y)), EqOf(Read(Cat(v, z), p), Read(z, y)))))));
        Formula lookup = All("v", word, All("z", word, All("P", t,
            EqOf(Sub(Cat(v, z), p), Call("bind", Sub(v, p), Call("nav", z))))));
        Formula leafNode = All("P", t, All("u", word, All("b", boolean,
            Imp(EqOf(Read(u, p), Call("reply", b)), EqOf(Sub(u, p), SomeOf(Call("atom", b)))))));
        Formula alphaSem = All("P", t, All("u", word, IffOf(InOf(u, Call("alpha", p)), EqOf(Read(u, p), alpha))));
        return And(classification, small, rows, unique, historyBlocks, overlap, zero, absent, leafPrefix,
            contexts, gammaShape, gammaBlocks, singleton, And(readNone, readSome), lookup, leafNode, alphaSem);
    }
}
