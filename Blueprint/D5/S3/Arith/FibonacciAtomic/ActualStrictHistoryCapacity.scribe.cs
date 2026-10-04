using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualStrictHistoryCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict actual leaf growth bounds the capacity of positive same-size families, through exact native recipe continuations.",
        H("Actual Strict History Capacity and Native Recipe Continuations"),
        Blocks(
            Paragraph(Text("Source is the original finite ordered alpha/beta tree. An address is a finite left/right word, including the empty root. "
                + "An event carries one address and its original four-valued reply. F is any family indexed by Fin(m), S is a finite index set, "
                + "and r is one Recipe(F,S) from ActualJointResponseCostCore. The continuation theorem requires neither positivity nor injectivity nor a common leaf size.")),
            Paragraph(Text("route(r,i) is that recipe's existing actual routeTrace. queue(F,S,H) retains exactly the indices in S whose actual trees "
                + "match every addressed report in H, including branch and absent reports. A history is live when it is a prefix of route(r,i) for some i in S. "
                + "res(r,H) starts with r; each event must use the current split's one full-vector representative and a nonempty survivor fiber. "
                + "It then selects exactly next(y,hy). A singleton has no transition. A residual R stores its finite queue Q(R) and its native recipe q(R).")),
            Paragraph(Text("child(R,e) is false at a singleton. At a split with actual vector a on queue T, it means that e's address equals "
                + "representative(F,a) and the fiber {i in T : a(i)=reply(e)} is nonempty. Thus the live children are precisely the nonempty fibers "
                + "of the original alpha, beta, branch and absent reports; all use the same representative. Concatenation is denoted cat, and prefix is ordinary list prefix.")),
            Describe.Lean(DescribeId.Create("native-recipe-reached-prefix"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity.reached_prefix"),
                H("Exact selected continuation and terminal prefix antichain"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Induction runs on the original Recipe with a motive universal over reached histories. At a split, a nonempty prefix's "
                        + "first event identifies its representative and original reply fiber. Every prototype matching that event enters the same selected "
                        + "next(y,hy). The child induction hypothesis transports its exact all-report queue, prefix membership and suffix identity back to the parent.")),
                    Paragraph(Text("Appending any further history after H is exactly descent from q(R); the option-valued selection makes the continuation unique "
                        + "among continuations selected by r. This asserts no uniqueness of arbitrary recipes on a finite set. The immediate-extension equivalence "
                        + "identifies every live addressed child. At a singleton it forbids every live extension and the suffix identity makes H the terminal route itself.")),
                    Paragraph(Text("If one terminal route prefixes another, the selected residual of the first has an empty route for its surviving index. "
                        + "A split cannot have an empty route on a member of its queue. Hence that residual is a singleton, and both indices are the same. "
                        + "This supplies terminal injection and a prefix antichain without an assumed route encoding.")),
                    Paragraph(Text("The continuation theorem carries the actual survivor history into the strict-growth and resource-budget arguments of the capacity theorem below."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-strict-history-capacity"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity.result"),
                H("Complete source31.7 capacity bound"),
                StatementSource.FromAuthor(CapacityFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix any natural m greater than zero and an injective actual family F:Fin(m)->Source, with every tree positive and native leaf count n. "
                        + "K(F) consists of index subsets on which one full-domain Strategy attains each tree's individual leaf baseline. Kcircle(m) contains exactly the empty and singleton subsets. "
                        + "The output-alpha maximum s(F) is max_i card(alphaLeaves(F(i))). The integer count is exactly source30.11: M(0,t)=M(r,0)=1 and "
                        + "M(r+1,t+1)=M(r,t+1)+2*M(r+1,t). Its first native representation supplies no separate mathematical content.")),
                    Paragraph(Text("A conflicting shared alpha/beta leaf would yield a native two-prototype Recipe with zero response gain, and hence one strategy jointly attaining both individual baselines. "
                        + "This contradicts K=Kcircle. Thus the original complex equality supplies non-conflict internally, without an eleven-leaf restriction or an added target premise. "
                        + "The finite nonempty actual cost core attains its minimum; the chosen strategy is exactly recipeStrategy for the minimizing strict Recipe.")),
                    Paragraph(Text("At every reached history, f and c count distinct acquired leaf and nonleaf addresses. Geometry is applied to that same history and actual survivor source. "
                        + "For a new decoded A block use its LR alpha anchor; for a C use its RR alpha anchor. If the anchor were covered, old compatibility and the five forcing rows "
                        + "would fix the new block and its report on all old survivors, contradicting strictness. The finite alpha union therefore grows at every strict leaf child, giving g>=f. "
                        + "When f>=s-1, at most one alpha remains uncovered. Complete same-size history rigidity makes the queue a singleton.")),
                    Paragraph(Text("Non-conflict allows at most one leaf-report child and at most the branch and absent children. Strictness supplies a nonleaf successor. "
                        + "Every prototype terminal has c<=t, so an internal queue must have c<t as well as f<s-1. The budget B(H) is M(s-1-f(H),t-c(H)) exactly on prefixes of actual "
                        + "terminal traces and zero elsewhere. For every history and every finite selection of addressed children, singleton queues have no live extension; strict queues have the "
                        + "one-leaf/two-nonleaf partition and positive remaining budgets. The original recurrence proves the required local child sum. FinitePrefixAntichainBudget then bounds "
                        + "the actual terminal antichain, whose cardinality equals m by native terminal index injection. This includes s=1, t=0 and every feasible small n.")),
                    Paragraph(Text("Only actually acquired addresses, whether leaf or nonleaf, enter the cache; inferred leaves do not. On a prototype, nonleafPaid(route) is exactly paid(route) minus its actual leaf set, and the terminal cost is n+c. "
                        + "The existing controller still verifies all n labelled leaves, paying f+c+(n-f)=n+c; inferred block leaves are not cache entries. Its independently initialized acquisition "
                        + "fallback retains the real outer cache and processes every finite unknown Source. Positivity, size and family membership restrict evaluation prototypes only.")),
                    Paragraph(Text("The W and Wu substitutions retain the original ALL-Source wrong-return and divergence contract. Source countability follows from existing finite composition fibers. "
                        + "One common good seed gives a globally correct total Strategy; execution uniqueness identifies independently chosen terminal runs. Integral monotonicity keeps the same law "
                        + "and the maximum inside the integral. Constant controllers use PUnit at the arbitrary seed universe and the actual completed unit interval, including endpoints. "
                        + "No expectation/maximum exchange or R/Ru assertion enters the theorem."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula EqOf(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula InOf(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, Par(y));
    private static Formula IffOf(Formula x, Formula y) => Seq(Par(x), Sp, Iff, Sp, Par(y));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string n, Formula type, Formula body) =>
        Seq(Exists, Sp, V(n), Colon, Sp, type, Comma, Sp, Par(body));

    private static Formula ResultFormula()
    {
        Formula m = V("m"), f = V("F"), s = V("S"), r = V("r"), h = V("H"), k = V("K");
        Formula rr = V("R"), rp = V("Rp"), i = V("i"), j = V("j"), e = V("e");
        Formula indices = Call("Fin", m), histories = Call("Hist"), residuals = Call("Residual", f);
        Formula Route(Formula q, Formula x) => Call("route", q, x);
        Formula Prefix(Formula a, Formula b) => Call("prefix", a, b);
        Formula Cat(Formula a, Formula b) => Call("cat", a, b);
        Formula Q = Call("Q", rr), qR = Call("q", rr);
        Formula Live = Some("i", indices, And(InOf(i, s), Prefix(h, Route(r, i))));
        Formula PrefixLaw = All("i", indices, Imp(InOf(i, s), IffOf(Prefix(h, Route(r, i)), InOf(i, Q))));
        Formula SuffixLaw = All("i", indices, Imp(InOf(i, Q), EqOf(Route(r, i), Cat(h, Route(qR, i)))));
        Formula AppendLaw = All("K", histories, EqOf(Call("res", r, Cat(h, k)), Call("res", qR, k)));
        Formula UniqueLaw = All("Rp", residuals, Imp(EqOf(Call("res", r, h), Call("some", rp)), EqOf(rp, rr)));
        Formula ChildLaw = All("e", Call("Event"), IffOf(
            Some("i", indices, And(InOf(i, s), Prefix(Cat(h, Call("one", e)), Route(r, i)))),
            Call("child", rr, e)));
        Formula Correspondence = All("H", histories, Imp(Live, Some("R", residuals, And(
            EqOf(Call("res", r, h), Call("some", rr)), EqOf(Q, Call("queue", f, s, h)),
            PrefixLaw, SuffixLaw, AppendLaw, UniqueLaw, ChildLaw))));
        Formula Terminal = All("i", indices, All("j", indices,
            Imp(And(InOf(i, s), InOf(j, s), Prefix(Route(r, i), Route(r, j))), EqOf(i, j))));
        return All("m", Call("Nat"), All("F", Call("Family", m),
            All("S", Call("Finset", indices), All("r", Call("Recipe", f, s), And(Correspondence, Terminal)))));
    }
    private static Formula CapacityFormula()
    {
        Formula m = V("m"), f = V("F"), n = V("n"), t = V("t");
        Formula bound = Seq(n, Sp, Plus, Sp, t);
        Formula Le(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
        Formula Or(params Formula[] xs) => Seq(xs.Select((x, i) =>
            i == 0 ? Par(x) : Seq(Sp, Lor, Sp, Par(x))).ToArray());
        Formula premises = And(Call("positiveIndex", m), Call("positiveFamily", f),
            Call("injective", f), Call("sameLeafSize", f, n),
            EqOf(Call("K", f), Call("Kcircle", m)),
            Or(Le(Call("D", f), bound), Le(Call("W", f), bound), Le(Call("Wu", f), bound)));
        Formula conclusion = Le(m, Call("M", Seq(Call("s", f), Sp, Minus, Sp, D(1)), t));
        return All("m", Call("Nat"), All("F", Call("Family", m), All("n", Call("Nat"),
            All("t", Call("Nat"), Imp(premises, conclusion)))));
    }

}
