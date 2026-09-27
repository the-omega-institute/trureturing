using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class ResidueFirstStepOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original rational cost attains its minimum over all eventually terminating deterministic "
            + "history selectors, with exact sibling first-step recurrences.",
        H("Terminal Histories and Exact First-Step Costs"),
        Blocks(
            Paragraph(Text(
                "Fix a prime p, a natural exponent e, and X=ZMod(p^e). The prior mu:X->Q is "
                    + "strictly positive at every state and has total mass one. Put q(c,a)=residueReadout(p,e,c,a) "
                    + "and m(S)=sum of mu(a) over a in S. Every cost below uses this original mu. "
                    + "Fin(X) denotes finite subsets of X; X itself also denotes the full finite set "
                    + "when used as an argument of m or K. For d<=e, B(d,j) is the full projection "
                    + "fiber with label j in Z(d)=ZMod(p^d). Ch(d,b) is the set of next-depth labels "
                    + "over b, and S(d,I) is the union of B(d+1,j) for j in I. Write "
                    + "C(d,j)=B(d+1,j) and E(d,I,j)=S(d,I with j removed).")),
            Paragraph(Text(
                "Let L=List(X times N), Sel=L->Option(X), and Tree=PassiveProtocol(X,constant N). "
                    + "A tree is inductively well-founded; its infinitely many possible natural-answer "
                    + "branches need not have a common depth bound. Run(T,a) is the entire list of "
                    + "center-answer pairs obtained from runPassiveProtocol(q,T,a). Trace(T,a) is the "
                    + "same run before conversion from Sigma responses to pairs. Length is preserved "
                    + "by that conversion. U(D,n,P) is the existing unroll, permitting n further "
                    + "queries after the chronological prefix P. Term(D,P,a,H) means legal(D,P,H), "
                    + "q(c,a)=r for every (c,r) in H, and D(P++H)=none. It requires actual stopping, "
                    + "not just exhaustion of n. Lengths count only H, never the prefix P.")),
            Paragraph(Text(
                "D_T is treeSelector(T): a stopped tree returns none on every history; a query "
                    + "node with center c returns some c on the empty history, and on (c',r)::H "
                    + "follows its r branch if c'=c, otherwise returning none. Extra records after "
                    + "a stopped node also return none. A matching but impossible answer follows "
                    + "the given branch. General source selectors D remain arbitrary: repeated, "
                    + "outside, useless, and post-identification queries are allowed, and termination "
                    + "is required only on the finite set under consideration.")),
            Paragraph(Text(
                "PC(S,P) is the set of rational values sum over a in S of mu(a)*length(H(a)), "
                    + "where D ranges over Sel and H ranges over functions X->L, every H(a) for "
                    + "a in S satisfies Term(D,P,a,H(a)), and zero error means that for every "
                    + "a,b in S and every common L0, Term(D,P,a,L0) and Term(D,P,b,L0) imply a=b. "
                    + "There is no condition on H outside S. TC(S) is the set of sums of "
                    + "mu(a)*length(Trace(T,a)) over S for all trees T whose traces distinguish "
                    + "every pair of states in S. These two sets are defined independently. "
                    + "Unique terminal histories make their lengths exactly the actual stopping counts.")),
            Paragraph(Text(
                "In the formula, Values(I,j->f(j)) denotes the set of f(j) for j in I, "
                    + "and Divide(A,m) denotes the set of w/m for w in A. Least(A,k) means "
                    + "IsLeast(A,k), including membership, so every minimum displayed is attained. "
                    + "The bracketed lists are conjunctions. All notation is relative to the "
                    + "quantified p,e,mu; every D,P,a,H,n and every state set is quantified explicitly.")),
            Describe.Lean(
                DescribeId.Create("residue-first-step-optimality"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/ResidueFirstStepOptimality.residue_first_step_optimality"),
                H("Exact selector costs, attained minima, and sibling recurrences"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Terminal persistence is an induction on the legal suffix, allowing an arbitrary "
                            + "prefix and any larger horizon. The converse follows the residual selector "
                            + "through chronological prefixes by tree recursion. Two terminal histories "
                            + "for the same target agree at a common larger horizon. Taking the maximum "
                            + "of the realized lengths on a finite set gives simultaneous equality of "
                            + "complete traces and counts for every sufficiently large horizon. This "
                            + "maximum never ranges over all syntactic answer branches.")),
                    Paragraph(Text(
                        "A separating query tree exists because center a separates a from every "
                            + "different state: its top-depth answer characterizes equality. At e=0, "
                            + "the carrier is a singleton and the stopped tree suffices. For each finite "
                            + "S, multiply all costs by the positive product of the rational denominators "
                            + "on S. The resulting objective is a natural-number weighted sum of actual "
                            + "query counts and therefore has an attained minimum. Positive scaling "
                            + "preserves the original rational ordering. The exact trace correspondence "
                            + "then gives attainment for all source selectors, at every prefix P.")),
                    Paragraph(Text(
                        "An optimum on a sibling state with more than one leaf cannot stop or begin "
                            + "outside that state. An outside center has a constant answer, and deleting "
                            + "it preserves identification while subtracting the strictly positive mass "
                            + "of the state. For a center in child C, the parent-depth answer leaves "
                            + "exactly the complementary sibling set E. Restricting the optimum to C already "
                            + "includes the first query; restricting its miss branch to E leaves one "
                            + "additional query for each target in E.")),
                    Paragraph(Text(
                        "For a nonleaf C, take its attained internal tree query(c,next) with c in C "
                            + "and an attained tree R for E. The splice query(c,r->if r=d then R else "
                            + "next(r)) has exactly the internal tree's complete trace on C. On E its "
                            + "trace is (c,d) followed by R's trace. It identifies the union, with cost "
                            + "K(C)+K(E)+m(E). Thus only the complement pays the extra entry query. "
                            + "When I has one nonleaf child, the state is that child itself and there "
                            + "is no extra entry charge. For leaf children and at least two active "
                            + "labels, every target pays the first query, giving m(S)+K(E); a singleton "
                            + "leaf requires zero queries.")),
                    Paragraph(Text(
                        "The normalized full-root minimum E_mu(p,e) is K(X), since PC(X,[]) is "
                            + "precisely its source cost set and m(X)=1. For every nonempty S, dividing "
                            + "by its positive original mass gives the attained conditional minimum "
                            + "K(S)/m(S). Empty S has cost zero, and e=0 also has root cost zero. "
                            + "The result makes no claim about finite-horizon assignments, pointwise "
                            + "scheduling order, or algorithmic complexity."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string name, params Formula[] args) => Call(name, args);
    private static Formula Par(Formula a) => Seq(Left, Open, a, Right, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Rightarrow, Sp, Par(b));
    private static Formula All(Formula a, Formula domain, Formula body) =>
        Seq(Forall, Sp, a, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula a, Formula domain, Formula body) =>
        Seq(Exists, Sp, a, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula And(params Formula[] clauses) => Seq(Left, OpenBracket,
        new Formula.Aligned([.. clauses.Select((clause, index) =>
            index == 0 ? Par(clause) : Seq(Land, Sp, Par(clause)))]), Right, CloseBracket);
    private static Formula Single(Formula a) => Seq(OpenBrace, a, CloseBrace);
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Arrow(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula Lambda(Formula a, Formula b) => Seq(a, Sp, Mapsto, Sp, b);
    private static Formula Nonempty(Formula a) => Seq(a, Sp, Neq, Sp, Emptyset);

    private static Formula Statement()
    {
        var p = V("p"); var e = V("e"); var d = V("d"); var b = V("b"); var i = V("I");
        var j = V("j"); var a = V("a"); var h = V("H"); var l = V("L0"); var prefix = V("P");
        var policy = V("D"); var tree = V("T"); var n = V("n"); var bigN = V("N");
        var s = V("S"); var k = V("K"); var mu = V("mu"); var x = V("X");
        var nat = Seq(Mathbb, Grp(V("N"))); var rat = Seq(Mathbb, Grp(V("Q")));
        var hist = V("L"); var sel = V("Sel"); var trees = V("Tree"); var fin = C("Fin", x);
        Formula Term(Formula hh) => C("Term", policy, prefix, a, hh);
        Formula Len(Formula hh) => C("length", hh);
        Formula Run(Formula t) => C("Run", t, a);
        Formula Unroll(Formula nn) => C("U", policy, nn, prefix);
        Formula Mass(Formula ss) => C("m", ss);
        Formula K(Formula ss) => C("apply", k, ss);
        Formula Least(Formula set, Formula v) => C("Least", set, v);
        Formula PC(Formula ss) => C("PC", ss, prefix);
        Formula TC(Formula ss) => C("TC", ss);
        var next = Seq(d, Plus, D(1));
        var sibling = C("S", d, i); var child = C("C", d, j); var complement = C("E", d, i, j);
        var persistence = All(policy, sel, All(prefix, hist, All(a, x, All(h, hist, All(n, nat,
            Imp(And(Term(h), Le(Len(h), n)), Equal(Run(Unroll(n)), h)))))));
        var uniqueness = All(policy, sel, All(prefix, hist, All(a, x, All(h, hist, All(l, hist,
            Imp(And(Term(h), Term(l)), Equal(h, l)))))));
        var converse = All(tree, trees, All(a, x,
            C("Term", C("treeSelector", tree), C("nil"), a, Run(tree))));
        var uniform = All(s, fin, All(policy, sel, All(prefix, hist,
            Imp(All(a, s, Some(h, hist, Term(h))), Some(bigN, nat,
                All(n, nat, Imp(Le(bigN, n), All(a, s, All(h, hist,
                    Imp(Term(h), And(Equal(Run(Unroll(n)), h),
                        Equal(Len(C("Trace", Unroll(n), a)), Len(h)))))))))))));
        var equality = All(s, fin, All(prefix, hist, Equal(PC(s), TC(s))));
        var nonleafValue = Seq(K(child), Plus, K(complement), Plus, Mass(sibling), Minus, Mass(child));
        var leafValue = Seq(Mass(sibling), Plus, K(complement));
        var recurrence = All(d, nat, Imp(Less(d, e), All(b, C("Z", d), All(i, C("Fin", C("Z", next)),
            Imp(And(Nonempty(i), Seq(i, Sp, Subseteq, Sp, C("Ch", d, b))), And(
                Imp(Less(next, e), Least(C("Values", i, Lambda(j, nonleafValue)), K(sibling))),
                Imp(And(Equal(next, e), Equal(C("card", i), D(1))), Equal(K(sibling), D(0))),
                Imp(And(Equal(next, e), Le(D(2), C("card", i))),
                    Least(C("Values", i, Lambda(j, leafValue)), K(sibling)))))))));
        var optimum = Some(k, Arrow(fin, rat), And(
            All(s, fin, All(prefix, hist, Least(PC(s), K(s)))),
            All(s, fin, Least(TC(s), K(s))),
            Equal(K(Emptyset), D(0)), All(a, x, Equal(K(Single(a)), D(0))),
            Imp(Equal(e, D(0)), Equal(K(x), D(0))),
            All(s, fin, All(prefix, hist, Imp(Nonempty(s),
                Least(C("Divide", PC(s), Mass(s)), Ratio(K(s), Mass(s)))))),
            All(d, nat, Imp(Less(d, e), All(j, C("Z", next),
                Equal(K(C("S", d, Single(j))), K(child))))),
            recurrence));
        return Disp(All(Seq(p, Comma, e), nat, Imp(C("Prime", p),
            All(mu, Arrow(x, rat), Imp(And(All(a, x, Less(D(0), C("apply", mu, a))),
                Equal(Mass(x), D(1))), And(persistence, uniqueness, converse, uniform, equality, optimum))))));
    }
}
