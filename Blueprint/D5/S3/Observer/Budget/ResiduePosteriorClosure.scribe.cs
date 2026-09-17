using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class ResiduePosteriorClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual longest-congruence queries preserve singleton or sibling states, and conditioning "
            + "a strictly positive rational prior on the executed history gives exactly those candidates.",
        H("Exact Residue Fibers and Adaptive Posteriors"),
        Blocks(
            Paragraph(Text(
                "Fix any prime p and any natural exponent e, including zero. Write X for ZMod(p^e), "
                    + "and let mu assign a strictly positive rational mass to every element of X, "
                    + "with total mass one. Write m(U) for the sum of mu over U and emb for the "
                    + "nonnegative extended-real embedding of a nonnegative rational number. "
                    + "The query h(c,a) is the existing residueReadout: the maximum of all k from "
                    + "zero through e for which the natural representatives agree modulo p^k. "
                    + "For each fixed p,e, put Z(k)=ZMod(p^k) for k in N and X=Z(e). The map "
                    + "pi(k,a), for k<=e and a in X, is primePowerProjection from precision e to k.")),
            Paragraph(Text(
                "For d<=e and b in Z(d), B(d,b) is the complete fiber pi(d,a)=b. "
                    + "For d<e and b in Z(d), Ch(d,b) consists of all "
                    + "labels modulo p^(d+1) reducing to b. For any I in Fin(Z(d+1)), S(d,I) "
                    + "is the union of their complete fibers in X. Empty I is permitted in a "
                    + "fiber formula; a sibling state requires I nonempty. For every S in Fin(X), c in X, and r in N, define "
                    + "F(S,c,r) as the elements a of S with h(c,a)=r, and R(c,r)=F(X,c,r). "
                    + "For t<e and c in X, J(t,c) is Ch(t,pi(t,c)) with pi(t+1,c) removed. "
                    + "Shape(U) means that U is a singleton or S(d,I) for some d<e, parent b, "
                    + "and nonempty I contained in Ch(d,b).")),
            Paragraph(Text(
                "A selector D takes the entire chronological list of pairs (center,response) "
                    + "and returns either the next center or none to stop. For each such D, "
                    + "natural n, and starting history P, U(D,n,P) is its "
                    + "finite unrolling into PassiveProtocol, beginning with accumulated history P "
                    + "and allowing n further queries. A query appends its actual reply before "
                    + "the next selection. Trace denotes runPassiveProtocol with h. Run is Trace followed by "
                    + "the pointwise conversion from Sigma responses to pairs. Legal(D,P,H) "
                    + "means each center in H is selected by D on P followed by exactly the "
                    + "earlier pairs of H. C(H) is the intersection of the recorded reply equations. "
                    + "A(D,H) is defined separately as the targets whose actual run U(D,|H|,[]) "
                    + "equals H. It does not use C(H). Write L=List(X times N) and Sel for the maps "
                    + "from L to Option(X); nil is the empty history and snoc(H,c,r) appends "
                    + "the pair (c,r). Every history variable below ranges over L.")),
            Paragraph(Text(
                "In the formula, apply(f,a) means f(a), and Fin(Y) denotes the finite subsets of Y, Union(I,f) the union "
                    + "of f(j) over j in I, and range(e+1) the natural numbers zero through e. "
                    + "For every finite T contained in X, m(T) is the sum of mu(a) over a in T; "
                    + "for every PMF P on X, prob(P,T) is the sum of P(a) over a in T. "
                    + "Supported(P,T) means there exists a in T belonging to support(P). "
                    + "The expression filter(P,T,hs) denotes PMF.filter using a witness hs of "
                    + "Supported(P,T). The witnesses hn, hs, hF, hR in the formula respectively "
                    + "certify normalization and the indicated support intersections. "
                    + "A let binding extends only over its bracketed body; each bracketed list "
                    + "is an explicit conjunction. All notation in the formula is relative to "
                    + "its quantified p,e,mu; no history or response is fixed implicitly.")),
            Describe.Lean(
                DescribeId.Create("residue-posterior-closure"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/ResiduePosteriorClosure.residue_posterior_closure"),
                H("Complete fibers, execution events, and conditioning"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed assertions hold for all objects in the indicated ranges. "
                            + "Every complete node at depth d has p^(e-d) leaves. Every nonleaf "
                            + "parent has exactly p children, these complete child fibers are "
                            + "pairwise disjoint, and their union is the parent. S(d,I) is their "
                            + "union for every I. The root at depth zero is all X for every root label, "
                            + "so a center outside that parent is impossible.")),
                    Paragraph(Text(
                        "For every d<e, parent b, I contained in Ch(d,b), and center c, "
                            + "S(d,I) is contained in B(d,b). If c is in B(d,b) but outside S(d,I), "
                            + "all current targets answer d. If c is outside B(d,b), choose any "
                            + "b0 in that complete parent: h(c,b0)<d and h(c,a)=h(c,b0) for every "
                            + "a in B(d,b). For nonempty I and c outside S(d,I), precisely one "
                            + "response fiber is S(d,I) and every other response fiber is empty.")),
                    Paragraph(Text(
                        "If c belongs to S(d,I), its child label is pi(d+1,c). The depth-d "
                            + "fiber is S(d,I with that label removed), including when it is empty; "
                            + "it is nonempty exactly when another active child remains. For every "
                            + "d<t<e the response-t fiber is S(t,J(t,c)), with exactly p-1 complete "
                            + "nonpath children and positive cardinality. The response-e fiber is "
                            + "the singleton c; responses below d or above e have empty fibers. "
                            + "For every finite S, all distinct response fibers are disjoint and "
                            + "the fibers indexed from zero through e exhaust S.")),
                    Paragraph(Text(
                        "Each active child of a depth-d parent has the same remaining height "
                            + "e-(d+1) and exactly p^(e-(d+1)) leaves. If d+1=e, every active child "
                            + "has one leaf. Otherwise d+1<e and every active child has more than "
                            + "one leaf. This quantifies over every active child, including a layer "
                            + "with only one active child. Such a child can still be nonleaf. "
                            + "Different response fibers may belong to different depths.")),
                    Paragraph(Text(
                        "The execution equivalence holds for every starting history P, every "
                            + "continuation H, and every target. The prefix identity holds for "
                            + "every n<=m and also before conversion of Sigma responses to pairs. "
                            + "For every legal H, A(D,H)=C(H). If D selects c after H, then "
                            + "A(D,H followed by (c,r)) equals F(C(H),c,r). No equation identifies "
                            + "an intermediate prefix with a completed longer transcript.")),
                    Paragraph(Text(
                        "Every nonempty candidate set C(H), even before choosing a selector, "
                            + "has Shape. At e=0, X is the singleton zero and mu assigns it mass "
                            + "one. At positive e, X is the union of all p first children. "
                            + "A nonempty response fiber of a singleton equals that singleton. "
                            + "Induction on chronological extensions uses the exact fibers and "
                            + "does not require strict shrinkage. Thus repetitions, constant queries, "
                            + "arbitrary history adaptation, stopping, and singleton continuations "
                            + "are all allowed; every finite prefix of a terminating strategy is included.")),
                    Paragraph(Text(
                        "The prior is PMF.ofFintype applied to emb(mu(a)), with its normalization "
                            + "proved from the rational total. Its support is all X. For any D,H "
                            + "with m(A(D,H))>0, the theorem first derives Legal(D,[],H), then "
                            + "A(D,H)=C(H), nonemptiness, and Shape(C(H)). The posterior P is "
                            + "PMF.filter of that prior on the actual event A(D,H). Its support "
                            + "equals C(H). At each candidate a its value is emb(mu(a)/m(C(H))), "
                            + "and outside C(H) its value is zero.")),
                    Paragraph(Text(
                        "Every nonempty finite leaf set has positive original mass. In a positive "
                            + "current history, let F=F(C(H),c,r) be nonempty. The response "
                            + "probability, the sum of P on R(c,r), is emb(m(F)/m(C(H))) and is "
                            + "strictly positive. Filtering P on the raw response event R(c,r) "
                            + "equals filtering the original prior on F. Its values are "
                            + "emb(mu(a)/m(F)) on F and zero elsewhere. When D actually selects "
                            + "c, the operational extension equality identifies F with the next "
                            + "actual event as well. This is sequential conditioning of the original prior.")),
                    Paragraph(Text(
                        "For positive e, the bound, threshold, and top-depth equality follow from "
                            + "PrimePowerNonadaptiveResolution by identifying cast equality with equality "
                            + "of representative remainders. At e=0 these facts reduce to ZMod(1). "
                            + "Surjectivity of the natural projections and equal additive-homomorphism "
                            + "fiber sizes give the exact counts. The explicit fiber classification "
                            + "then drives the chronological induction. Strict positivity ensures "
                            + "conditioning removes no candidate except through a failed reply "
                            + "equation. Zero-mass priors are outside the assumptions: on two leaves, "
                            + "masses one and zero already give a probability support strictly "
                            + "smaller than the initial logical candidate set."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string name, params Formula[] args) => Call(name, args);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Implies(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Par(Formula a) => Seq(Left, Open, a, Right, Close);
    private static Formula Both(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Either(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula IffTo(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula NotMember(Formula a, Formula b) => Seq(Neg, Par(Member(a, b)));
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula AtMost(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula SubsetOf(Formula a, Formula b) => Seq(a, Sp, Subseteq, Sp, b);
    private static Formula Power(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Singleton(Formula a) => Seq(OpenBrace, a, CloseBrace);
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Positive(Formula a) => Less(D(0), a);
    private static Formula Nonempty(Formula a) => Seq(a, Sp, Neq, Sp, Emptyset);
    private static Formula All(Formula variables, Formula domain, Formula body) =>
        Seq(Forall, Sp, variables, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Witness(Formula variable, Formula proposition, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Par(proposition), Comma, Sp, body);
    private static Formula Let(Formula variable, Formula value, Formula body) =>
        Seq(V("let"), Sp, Equal(variable, value), Sp, V("in"), Sp, body);
    private static Formula AndBlock(params Formula[] clauses) => Seq(Left, OpenBracket,
        new Formula.Aligned([.. clauses.Select((clause, index) =>
            index == 0 ? Par(clause) : Seq(Land, Sp, Par(clause)))]), Right, CloseBracket);

    private static Formula Statement()
    {
        var p = V("p"); var e = V("e"); var d = V("d"); var t = V("t"); var k = V("k");
        var a = V("a"); var b = V("b"); var c = V("c"); var r = V("r"); var i = V("I");
        var j = V("j"); var b0 = V("b0"); var u = V("T"); var n = V("n"); var m = V("m");
        var x = V("X"); var h = V("H"); var q = V("Q"); var z = V("z"); var policy = V("D");
        var nat = Seq(Mathbb, Grp(V("N"))); var rat = Seq(Mathbb, Grp(V("Q")));
        var histories = V("L"); var selectors = V("Sel");
        var s = C("S", d, i); var parent = C("B", d, b); var ch = C("Ch", d, b);
        var next = Seq(d, Plus, D(1)); var path = C("pi", next, c);
        var erased = Seq(i, Sp, Setminus, Sp, Singleton(path));
        var cand = C("C", h); var actual = C("A", policy, h); var post = V("P");
        var prior = V("prior"); var hn = V("hn"); var hs = V("hs");
        var hF = V("hF"); var hR = V("hR"); var fiber = V("F"); var response = V("R");
        Formula Z(Formula depth) => C("Z", depth);
        Formula Fin(Formula domain) => C("Fin", domain);
        Formula Card(Formula set) => C("card", set);
        Formula Mass(Formula set) => C("m", set);
        Formula MuAt(Formula leaf) => C("mu", leaf);
        Formula Read(Formula leaf) => C("h", c, leaf);
        Formula Project(Formula depth, Formula leaf) => C("pi", depth, leaf);
        Formula Fiber(Formula set, Formula reply) => C("F", set, c, reply);
        Formula Support(Formula pmf) => C("support", pmf);
        Formula Supported(Formula pmf, Formula set) => C("Supported", pmf, set);
        Formula Filter(Formula pmf, Formula set, Formula witness) => C("filter", pmf, set, witness);
        Formula Prob(Formula pmf, Formula set) => C("prob", pmf, set);
        Formula Emb(Formula value) => C("emb", value);
        Formula Union(Formula labels, Formula variable, Formula term) =>
            C("Union", labels, Seq(variable, Sp, Mapsto, Sp, term));
        Formula Depth(Formula variable, Formula guard, Formula body) =>
            All(variable, nat, Implies(guard, body));
        Formula At(Formula function, Formula argument) => C("apply", function, argument);
        Formula Values(Formula pmf, Formula set) => All(a, x, AndBlock(
            Implies(Member(a, set), Equal(At(pmf, a), Emb(Ratio(MuAt(a), Mass(set))))),
            Implies(NotMember(a, set), Equal(At(pmf, a), D(0)))));

        var childPartition = Depth(d, Less(d, e), All(b, Z(d), AndBlock(
            Equal(Card(ch), p),
            Equal(Union(ch, j, C("B", next, j)), parent),
            All(Seq(j, Comma, k), Z(next), Implies(Seq(j, Sp, Neq, Sp, k),
                C("Disjoint", C("B", next, j), C("B", next, k)))),
            All(i, Fin(Z(next)), Equal(s, Union(i, j, C("B", next, j)))))));
        var geometry = Depth(d, Less(d, e), All(b, Z(d), All(i, Fin(Z(next)),
            Implies(SubsetOf(i, ch), All(c, x, AndBlock(
                All(a, s, Member(a, parent)),
                Implies(Both(Member(c, parent), NotMember(c, s)), All(a, s, Equal(Read(a), d))),
                Implies(NotMember(c, parent), All(b0, parent, AndBlock(
                    Less(Read(b0), d), All(a, parent, Equal(Read(a), Read(b0)))))),
                Implies(Member(c, s), AndBlock(
                    Equal(Fiber(s, d), C("S", d, erased)),
                    Depth(t, Both(Less(d, t), Less(t, e)), Equal(Fiber(s, t), C("S", t, C("J", t, c)))),
                    Equal(Fiber(s, e), Singleton(c)),
                    All(r, nat, Implies(Either(Less(r, d), Less(e, r)), Equal(Fiber(s, r), Emptyset))),
                    IffTo(Nonempty(Fiber(s, d)), Nonempty(erased))))))))));
        var outside = Depth(d, Less(d, e), All(b, Z(d), All(i, Fin(Z(next)),
            Implies(Both(Nonempty(i), SubsetOf(i, ch)), All(c, x,
                Implies(NotMember(c, s), Seq(Exists, Sp, r, Sp, InMacro, Sp, nat, Comma, Sp,
                    AndBlock(AtMost(r, e), All(t, nat, AndBlock(
                        Implies(Equal(t, r), Equal(Fiber(s, t), s)),
                        Implies(Seq(t, Sp, Neq, Sp, r), Equal(Fiber(s, t), Emptyset))))))))))));
        var nonpath = Depth(t, Less(t, e), All(c, x, AndBlock(
            Equal(Card(C("J", t, c)), Seq(p, Minus, D(1))),
            Nonempty(C("S", t, C("J", t, c))))));
        var partition = All(u, Fin(x), All(c, x, AndBlock(
            All(Seq(r, Comma, t), nat, Implies(Seq(r, Sp, Neq, Sp, t),
                C("Disjoint", Fiber(u, r), Fiber(u, t)))),
            Equal(Union(C("range", Seq(e, Plus, D(1))), r, Fiber(u, r)), u))));
        var noMixing = Depth(d, Less(d, e), All(i, Fin(Z(next)), AndBlock(
            All(j, i, Equal(Card(C("B", next, j)), Power(p, Seq(e, Minus, Par(next))))),
            Either(Both(Equal(next, e), All(j, i, Equal(Card(C("B", next, j)), D(1)))),
                Both(Less(next, e), All(j, i, Less(D(1), Card(C("B", next, j)))))))));
        var root = AndBlock(
            Implies(Equal(e, D(0)), Equal(x, Singleton(D(0)))),
            Implies(Positive(e), Equal(x, C("S", D(0), C("Ch", D(0), D(0))))),
            All(b, Z(D(0)), Equal(C("B", D(0), b), x)));
        var execution = All(policy, selectors, AndBlock(
            All(Seq(h, Comma, q), histories, All(a, x, IffTo(
                Equal(C("Run", C("U", policy, C("length", h), q), a), h),
                Both(C("Legal", policy, q, h), All(z, h, Equal(C("h", C("fst", z), a), C("snd", z))))))),
            All(Seq(n, Comma, m), nat, Implies(AtMost(n, m), All(q, histories, All(a, x,
                Equal(C("take", n, C("Trace", C("U", policy, m, q), a)),
                    C("Trace", C("U", policy, n, q), a)))))),
            All(h, histories, Implies(C("Legal", policy, C("nil"), h), Equal(actual, cand))),
            All(h, histories, All(c, x, All(r, nat,
                Implies(Both(C("Legal", policy, C("nil"), h), Equal(At(policy, h), C("some", c))),
                    Equal(C("A", policy, C("snoc", h, c, r)), Fiber(cand, r))))))));
        var sequential = All(c, x, All(r, nat,
            Let(fiber, Fiber(cand, r), AndBlock(Let(response, C("R", c, r), AndBlock(
                Implies(Nonempty(fiber), AndBlock(
                    Positive(Mass(fiber)),
                    Equal(Prob(post, response), Emb(Ratio(Mass(fiber), Mass(cand)))),
                    Positive(Prob(post, response)),
                    Witness(hF, Supported(prior, fiber),
                        Witness(hR, Supported(post, response), AndBlock(
                            Equal(Filter(post, response, hR), Filter(prior, fiber, hF)),
                            Values(Filter(prior, fiber, hF), fiber))))))))))));
        var posterior = Witness(hn,
            Equal(Seq(Sum, Underscore, Grp(Member(a, x)), Emb(MuAt(a))), D(1)),
            Let(prior, C("ofFintype", Seq(a, Sp, Mapsto, Sp, Emb(MuAt(a))), hn), AndBlock(
                Equal(Support(prior), x),
                All(policy, selectors, All(h, histories, Implies(Positive(Mass(actual)),
                    Witness(hs, Supported(prior, actual),
                        Let(post, Filter(prior, actual, hs), AndBlock(
                            C("Legal", policy, C("nil"), h), Equal(actual, cand),
                            Nonempty(cand), C("Shape", cand), Equal(Support(post), cand),
                            Values(post, cand), sequential)))))))));

        return Disp(All(Seq(p, Comma, e), nat, Implies(C("Prime", p),
            Let(x, C("ZMod", Power(p, e)), AndBlock(
                Let(histories, C("List", Seq(x, Times, nat)), AndBlock(
                    Let(selectors, Seq(histories, To, C("Option", x)), AndBlock(
                        All(V("mu"), Par(Seq(x, To, rat)), Implies(
                            AndBlock(All(a, x, Positive(MuAt(a))), Equal(Mass(x), D(1))),
                            AndBlock(
                                Depth(k, AtMost(k, e), All(Seq(a, Comma, c), x,
                                    IffTo(AtMost(k, Read(a)), Equal(Project(k, a), Project(k, c))))),
                                Depth(t, Less(t, e), All(Seq(a, Comma, c), x,
                                    IffTo(Equal(Read(a), t), Both(Equal(Project(t, a), Project(t, c)),
                                        Seq(Project(Seq(t, Plus, D(1)), a), Sp, Neq, Sp,
                                            Project(Seq(t, Plus, D(1)), c)))))),
                                All(Seq(a, Comma, c), x, IffTo(Equal(Read(a), e), Equal(a, c))),
                                Depth(d, AtMost(d, e), All(b, Z(d), Equal(Card(parent), Power(p, Seq(e, Minus, d))))),
                                childPartition, geometry, outside, nonpath, partition, noMixing, root,
                                All(Seq(b, Comma, c), x, All(r, nat,
                                    Implies(Nonempty(Fiber(Singleton(b), r)), Equal(Fiber(Singleton(b), r), Singleton(b))))),
                                All(h, histories, Implies(Nonempty(cand), C("Shape", cand))),
                                execution,
                                All(u, Fin(x), Implies(Nonempty(u), Positive(Mass(u)))),
                                Implies(Equal(e, D(0)), All(a, x, Equal(MuAt(a), D(1)))),
                                posterior))))))))))));
    }
}
