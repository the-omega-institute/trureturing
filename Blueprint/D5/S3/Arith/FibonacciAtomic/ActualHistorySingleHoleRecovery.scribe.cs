using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualHistorySingleHoleRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite leaf history with at most one uncovered alpha fixes every equal-size compatible actual third image.",
        H("Complete Leaf-History Rigidity and a Common Literal Output Hole"),
        Blocks(
            Paragraph(Text("T is the original FreeMagma Bool of nonempty finite ordered full binary trees. "
                + "True labels alpha and false labels beta; address bits false and true mean left and right. "
                + "All finite addresses, including the empty root, have the four replies alpha, beta, branch and absent. "
                + "Positive trees are actual third substitution images. E=pair(beta,alpha), "
                + "A=pair(E,beta), and C=pair(A,E). Their leaf counts are two, three and five.")),
            Paragraph(Text("History is any finite list of address/reply pairs, with repetitions permitted. "
                + "compatible(H,P) means that P is positive and matches exactly the alpha and beta reports in H. "
                + "Branch and absent reports impose no comparison constraint. blocks(H) is the finite set obtained "
                + "from those leaf reports by the five-row decoder of ActualLeafHistoryRigidity. "
                + "gamma(H) is the set union of alpha addresses in those blocks; overlaps are counted once. "
                + "unc(H,P) is alphaLeaves(P) minus gamma(H). No equal-size condition is part of compatibility.")),
            Paragraph(Text("Context is the finite literal OutputContext from ActualLeafHistoryRigidity, whose "
                + "left and right constructors store actual output siblings. hole(J) is its unique hole address "
                + "and plug(J,X) fills that hole. sub(h,P) is some(X) exactly when the actual subtree X exists "
                + "at h. Leaves(P) is the full labelled leaf frontier, with labels obtained by read(u,P). "
                + "root(d) is the root of a decoded block d; prefix is ordinary word prefix. "
                + "n(P) is the native leaf count, and card is finite-set cardinality.")),
            Describe.Lean(DescribeId.Create("actual-history-context-length"),
                DeclarationHandle.Create(Prefix + "context_length"),
                H("Leaf Count of a Filled Context"),
                StatementSource.FromAuthor(ContextLengthFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Filling the hole of a literal output context J with Z gives "
                    + "n(plug(J,Z))=outsideLeaves(J)+n(Z), by induction on the context: the hole adds nothing, "
                    + "and each left or right constructor adds the leaf count of its stored sibling."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-complete-rigidity"),
                DeclarationHandle.Create(Prefix + "complete_history_rigidity"),
                H("Zero Recovery, Size-Free Common Context, and Same-Size Rigidity"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If every alpha is covered, the previously established complete labelled-frontier "
                        + "recovery fixes the entire output tree without comparing sizes.")),
                    Paragraph(Text("For a singleton residual x, the native position classification chooses either "
                        + "an A at h with x=hLR, or the right E of a C at v with h=vR and x=vRR. "
                        + "In the second case the left A is already fixed. For each leaf outside h, locate its "
                        + "canonical A or C block. An A whose LR alpha differs from x is fixed; a C whose RR "
                        + "alpha differs from x is fixed. Equality identifies the special block by suffix "
                        + "cancellation. Its outside leaves are absent in the A case and belong to the fixed "
                        + "left A in the C case. Thus all outside labelled leaves match in every compatible tree.")),
                    Paragraph(Text("A forced A/C block meeting the A hole would contain x by block overlap. "
                        + "A block meeting the right E hole is either that C, which contains x, or its left A, "
                        + "which is disjoint from the hole. Hence every history block has an incomparable root "
                        + "to the selected hole. Replacing the reference subtree by a hole gives one context J "
                        + "before competitors are quantified. Complete sibling frontiers force each path branch, "
                        + "fix each literal sibling, and ensure the hole exists in every competitor. The empty "
                        + "path gives the root-hole case, including empty history on A.")),
                    Paragraph(Text("A common literal context has n(plug(J,Z))=outsideLeaves(J)+n(Z), proved by "
                        + "context induction. Equal total leaf counts cancel the common outside count. "
                        + "The competitor remains ambient positive, so an existing two-leaf hole subtree is E "
                        + "and a three-leaf hole subtree is A. No positivity of the hole subtree is assumed. "
                        + "Consequently its filling equals the reference filling, and the full trees are equal.")),
                    Paragraph(Text("With P=pair(A,A), H containing only the beta report at LR, and Pp=C=pair(A,E), "
                        + "the common context is right(A,hole). The fillings A and E have different sizes. "
                        + "This demonstrates why context recovery precedes and does not require the equal-size condition."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula InOf(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula NegOf(Formula a) => Seq(Neg, Sp, Par(a));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula OrOf(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));

    private static Formula ContextLengthFormula()
    {
        Formula j = V("J"), z = V("Z");
        return All("J", Call("Context"), All("Z", V("T"), EqOf(Call("n", Call("plug", j, z)),
            Seq(Call("outsideLeaves", j), Sp, Plus, Sp, Call("n", z)))));
    }

    private static Formula ResultFormula()
    {
        Formula history = Call("History"), tree = V("T"), word = Call("Word"), context = Call("Context");
        Formula hst = V("H"), p = V("P"), pp = V("Pp"), j = V("J"), h = V("h"), x = V("X"), y = V("Y");
        Formula u = V("u"), d = V("d");
        Formula Compatible(Formula q) => Call("compatible", hst, q);
        Formula Card = Call("card", Call("unc", hst, p));
        Formula Read(Formula q) => Call("read", u, q);
        Formula Outside = All("u", word, Imp(And(InOf(u, Call("Leaves", p)),
            NegOf(Call("prefix", h, u))), EqOf(Read(pp), Read(p))));
        Formula Blocks = All("d", Call("Block"), Imp(InOf(d, Call("blocks", hst)),
            And(NegOf(Call("prefix", Call("root", d), h)), NegOf(Call("prefix", h, Call("root", d))))));
        Formula Filling = Some("Y", tree, And(EqOf(Call("sub", h, pp), Call("some", y)),
            EqOf(Call("plug", j, y), pp)));
        Formula zero = Imp(EqOf(Card, D(0)), All("Pp", tree, Imp(Compatible(pp), EqOf(pp, p))));
        Formula one = Imp(EqOf(Card, D(1)), Some("J", context, Some("h", word, Some("X", tree,
            And(EqOf(Call("hole", j), h), OrOf(EqOf(x, V("A")), EqOf(x, V("E"))),
                EqOf(Call("sub", h, p), Call("some", x)), EqOf(Call("plug", j, x), p), Blocks,
                All("Pp", tree, Imp(Compatible(pp), And(Outside, Filling))))))));
        Formula rigid = Imp(LeOf(Card, D(1)), All("Pp", tree,
            Imp(And(Compatible(pp), EqOf(Call("n", pp), Call("n", p))), EqOf(pp, p))));
        return All("H", history, All("P", tree, Imp(Compatible(p), And(zero, one, rigid))));
    }
}
