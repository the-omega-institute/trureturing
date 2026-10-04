using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualImageSevenLeafSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct equal-size nonconflicting actual third Fibonacci images differ at at least seven leaf addresses on each side.",
        H("Seven-Leaf Separation of Actual Fibonacci Images"),
        Blocks(
            Paragraph(Text("T is FreeMagma Bool: nonempty finite free ordered full binary trees. "
                + "True labels alpha and false labels beta. No associativity, commutativity or quotient "
                + "identifications are imposed. The original substitution rho sends alpha to beta, "
                + "beta to pair(beta,alpha), and preserves the ordered pair constructor.")),
            Def("thirdImage", "Actual third image", "R(t)=rho^3(t), and I is exactly the range of R on T."),
            Def("leafAddresses", "Literal leaf addresses", "L(t) is a finite set of finite Boolean words. "
                + "It is the toFinset view of ActualTreeReadoutAcquisition.leaves(t). "
                + "False in a word means left and true means right. A leaf contributes the empty word; "
                + "pair(p,q) contributes the left-prefixed words of L(p) and the right-prefixed words of L(q)."),
            Def("leafLabel", "Labels at exact addresses", "label(t,u) is some(b) exactly when the "
                + "public ActualTreeReadoutAcquisition.readout(u,t) reports that leaf label. "
                + "Alpha projects to some(true), beta to some(false), and branch or absent to none."),
            Def("sharedLeaves", "Shared leaves", "s(p,q) counts literal addresses which are leaves "
                + "in both trees, irrespective of labels. Simultaneous recursion gives one for two leaves, "
                + "the sum of corresponding child counts for two branches, and zero for mixed root types."),
            Def("Nonconflict", "Shared-label compatibility", "NC(p,q) compares labels only at shared "
                + "leaf addresses. Mixed leaf/branch and leaf/absent reports impose no restriction."),
            Def("unsharedLeaves", "Unshared leaves", "n(p) is FreeMagma.length(p), and nu(p,q)=n(p)-s(p,q). "
                + "The theorem identifies these numbers with the exact finite address cardinalities."),
            Def("E", "Second alpha image", "E=pair(beta,alpha)."),
            Def("A", "Third alpha image", "A=pair(E,beta)=R(alpha)."),
            Def("C", "Third beta image", "C=pair(A,E)=R(beta)."),
            Def("pThirteen", "First original preimage", "p=pair(beta,pair(alpha,beta))."),
            Def("qThirteen", "Second original preimage", "q=pair(pair(alpha,beta),beta)."),
            Def("PThirteen", "First sharp image", "P=pair(C,pair(A,C)).", "pthirteen-image"),
            Def("QThirteen", "Second sharp image", "Q=pair(pair(A,C),C).", "qthirteen-image"),
            Def("sharpShared", "Exact shared labelled words", "H consists of (LLLL,beta), "
                + "(LLLR,alpha), (LLR,beta), (RLLL,beta), (RLLR,alpha), and (RLR,beta). "
                + "joint(p,q) maps each word in L(p) intersect L(q) to its pair with label(p,u).getD(false). "
                + "The leaf-address equivalence ensures that the default is never used there."),
            Paragraph(Text("card is finite-set cardinality, inter and diff are intersection and difference. "
                + "Word is the type of finite left/right words, Bool is the label type, and c counts alpha "
                + "first and beta second. The sharp pair proves attainment of the separation constant; "
                + "it makes no assertion of capacity equality.")),
            Describe.Lean(DescribeId.Create("actual-image-seven-leaf-separation"),
                DeclarationHandle.Create(Prefix + "seven_leaf_separation"),
                H("Universal Separation and Same-Composition Sharpness"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every actual third image has at least three leaves, and every image "
                        + "of a preimage other than alpha has at least five. A and C conflict at LR. "
                        + "Comparing A with pair(R(x),R(y)) is compatible exactly when x is not alpha; "
                        + "then the shared count is zero and the composite has at least eight leaves.")),
                    Paragraph(Text("For C against pair(R(x),R(y)), compatibility excludes y=alpha. "
                        + "If x=alpha, the shared count is three, leaving two leaves on the atomic side "
                        + "and at least five on the composite side. The case x=beta conflicts. "
                        + "A branching x reduces to the A comparison and has no shared leaves. "
                        + "Thus every legal atomic/composite pair has strictly increasing sizes, "
                        + "sizes at least three and eight, and unshared counts at least two and five.")),
                    Paragraph(Text("Induction on the actual preimages propagates four alternatives: "
                        + "equal images, either strict size orientation with those local bounds, or "
                        + "sizes at least eleven and both unshared counts at least seven. Exact address "
                        + "counts add across corresponding children. Opposite strict orientations give "
                        + "three plus eight leaves and two plus five unshared leaves on each side. "
                        + "A previously separated child remains separated. Distinct equal-size images "
                        + "therefore satisfy the fourth alternative. Equal sizes equate the two differences "
                        + "and give the shared-leaf upper bound.")),
                    Paragraph(Text("The two literal preimages produce P and Q. Each image contains one "
                        + "A and two C, giving composition (5,8) and thirteen leaves. Their six shared "
                        + "labelled addresses are exactly H, so each side has seven unshared leaves."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose, string? key = null) => Describe.Lean(
        DescribeId.Create("actual-image-" + (key ?? name.ToLowerInvariant())), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula InOf(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));

    private static Formula ResultFormula()
    {
        Formula p = V("p"), q = V("q"), u = V("u"), a = V("a"), b = V("b");
        Formula bigP = V("P"), bigQ = V("Q"), n = V("n");
        Formula tree = V("T"), word = Call("Word"), boolean = Call("Bool"), nat = Call("Nat");
        Formula L(Formula x) => Call("L", x);
        Formula N(Formula x) => Call("n", x);
        Formula S(Formula x, Formula y) => Call("s", x, y);
        Formula Nu(Formula x, Formula y) => Call("nu", x, y);
        Formula Label(Formula x) => Call("label", x, u);
        Formula SomeLabel(Formula x) => Call("some", x);
        Formula Ne(Formula x, Formula y) => Seq(x, Sp, Neq, Sp, y);
        Formula leafSemantics = All("p", tree, And(
            EqOf(Call("card", L(p)), N(p)),
            All("u", word, IffOf(InOf(u, L(p)),
                Some("b", boolean, EqOf(Label(p), SomeLabel(b)))))));
        Formula ncSemantics = IffOf(Call("NC", p, q),
            All("u", word, All("a", boolean, All("b", boolean,
                Imp(EqOf(Label(p), SomeLabel(a)),
                    Imp(EqOf(Label(q), SomeLabel(b)), EqOf(a, b)))))));
        Formula pairSemantics = All("p", tree, All("q", tree, And(
            EqOf(S(p, q), Call("card", Call("inter", L(p), L(q)))),
            EqOf(Nu(p, q), Call("card", Call("diff", L(p), L(q)))), ncSemantics)));
        Formula universal = All("P", tree, All("Q", tree, All("n", nat,
            Imp(And(InOf(bigP, V("I")), InOf(bigQ, V("I")), Ne(bigP, bigQ),
                EqOf(N(bigP), n), EqOf(N(bigQ), n), Call("NC", bigP, bigQ)),
                And(LeOf(D(1, 1), n), EqOf(Nu(bigP, bigQ), Nu(bigQ, bigP)),
                    LeOf(D(7), Nu(bigP, bigQ)),
                    LeOf(S(bigP, bigQ), Seq(n, Sp, Minus, Sp, D(7))))))));
        Formula sharp = And(
            EqOf(bigP, Call("R", p)), EqOf(bigQ, Call("R", q)), Ne(bigP, bigQ),
            Call("NC", bigP, bigQ),
            EqOf(Call("c", bigP), Pair(D(5), D(8))),
            EqOf(Call("c", bigQ), Pair(D(5), D(8))),
            EqOf(N(bigP), D(1, 3)), EqOf(N(bigQ), D(1, 3)), EqOf(S(bigP, bigQ), D(6)),
            EqOf(Nu(bigP, bigQ), D(7)), EqOf(Nu(bigQ, bigP), D(7)),
            EqOf(Call("joint", bigP, bigQ), V("H")));
        return Disp(Seq(Begin, Grp(V("gathered")),
            And(leafSemantics, pairSemantics, universal, sharp), End, Grp(V("gathered"))));
    }
}
