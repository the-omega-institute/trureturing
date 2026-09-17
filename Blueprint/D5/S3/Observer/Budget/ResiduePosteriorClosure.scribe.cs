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
                    + "The map pi(k,a) is primePowerProjection from precision e to k.")),
            Paragraph(Text(
                "B(d,b) is the complete fiber pi(d,a)=b. For d<e, Ch(d,b) consists of all "
                    + "labels modulo p^(d+1) reducing to b. For any set I of those labels, S(d,I) "
                    + "is the union of their complete fibers in X. Empty I is permitted in a "
                    + "fiber formula; a sibling state requires I nonempty. Define "
                    + "F(S,c,r) as the elements a of S with h(c,a)=r, and R(c,r)=F(X,c,r). "
                    + "For t<e, J(t,c) is Ch(t,pi(t,c)) with pi(t+1,c) removed. "
                    + "Shape(U) means that U is a singleton or S(d,I) for some d<e, parent b, "
                    + "and nonempty I contained in Ch(d,b).")),
            Paragraph(Text(
                "A selector D takes the entire chronological list of pairs (center,response) "
                    + "and returns either the next center or none to stop. U(D,n,P) is its "
                    + "finite unrolling into PassiveProtocol, beginning with accumulated history P "
                    + "and allowing n further queries. A query appends its actual reply before "
                    + "the next selection. Run denotes runPassiveProtocol with h, followed by "
                    + "the pointwise conversion from Sigma responses to pairs. Legal(D,P,H) "
                    + "means each center in H is selected by D on P followed by exactly the "
                    + "earlier pairs of H. C(H) is the intersection of the recorded reply equations. "
                    + "A(D,H) is defined separately as the targets whose actual run U(D,|H|,[]) "
                    + "equals H. It does not use C(H).")),
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
                        "The maximum characterization follows by retaining its zero-depth member "
                            + "and reducing congruence from a maximum depth to any smaller depth. "
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
    private static Formula Both(Formula a, Formula b) => Seq(a, Sp, Land, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Power(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Singleton(Formula a) => Seq(OpenBrace, a, CloseBrace);
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Positive(Formula a) => Seq(D(0), Sp, Lt, Sp, a);
    private static Formula Nonempty(Formula a) => Seq(a, Sp, Neq, Sp, Emptyset);
    private static Formula Statement()
    {
        var p = V("p"); var e = V("e"); var d = V("d"); var t = V("t"); var k = V("k");
        var a = V("a"); var b = V("b"); var c = V("c"); var r = V("r"); var i = V("I");
        var x = V("X"); var s = C("S", d, i); var h = V("H"); var policy = V("D");
        var cand = C("C", h); var actual = C("A", policy, h); var post = V("P");
        var fiber = C("F", cand, c, r); var response = C("R", c, r);
        var path = C("pi", Seq(d, Plus, D(1)), c);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, p, Comma, e, Comma, Mu, Comma, Sp,
                Both(C("Prime", p), Both(Seq(Forall, Sp, a, Sp, InMacro, Sp, x, Comma, Sp, Positive(C("mu", a))), Equal(C("m", x), D(1)))), Sp, Rightarrow),
            Seq(Forall, Sp, k, Sp, Leq, Sp, e, Comma, Sp, a, Comma, c, Comma, Sp,
                k, Sp, Leq, Sp, C("h", c, a), Sp, Iff, Sp, Equal(C("pi", k, a), C("pi", k, c))),
            Seq(Forall, Sp, t, Sp, Lt, Sp, e, Comma, Sp,
                Equal(C("h", c, a), t), Sp, Iff, Sp,
                Both(Equal(C("pi", t, a), C("pi", t, c)),
                    Seq(C("pi", Seq(t, Plus, D(1)), a), Sp, Neq, Sp, C("pi", Seq(t, Plus, D(1)), c)))),
            Seq(Equal(C("h", c, a), e), Sp, Iff, Sp, Equal(a, c)),
            Equal(C("card", C("B", d, b)), Power(p, Seq(e, Minus, d))),
            Equal(C("card", C("Ch", d, b)), p),
            Implies(Member(c, s), Equal(C("F", s, c, d), C("S", d, Seq(i, Sp, Setminus, Sp, Singleton(path))))),
            Seq(Member(c, s), Comma, Sp, d, Sp, Lt, Sp, t, Sp, Lt, Sp, e, Sp, Rightarrow, Sp,
                Equal(C("F", s, c, t), C("S", t, C("J", t, c)))),
            Equal(C("card", C("J", t, c)), Seq(p, Minus, D(1))),
            Implies(Member(c, s), Equal(C("F", s, c, e), Singleton(c))),
            Equal(C("card", C("B", Seq(d, Plus, D(1)), b)), Power(p, Seq(e, Minus, Open, d, Plus, D(1), Close))),
            Seq(Equal(C("Run", C("U", policy, C("length", h), V("Q")), a), h), Sp, Iff, Sp,
                Both(C("Legal", policy, V("Q"), h), Seq(Forall, Sp, V("z"), Sp, InMacro, Sp, h, Comma,
                    Equal(C("h", C("fst", V("z")), a), C("snd", V("z")))))),
            Seq(V("n"), Sp, Leq, Sp, V("m"), Sp, Rightarrow, Sp,
                Equal(C("take", V("n"), C("Run", C("U", policy, V("m"), V("Q")), a)),
                    C("Run", C("U", policy, V("n"), V("Q")), a))),
            Implies(C("Legal", policy, C("nil"), h), Equal(actual, cand)),
            Implies(Nonempty(cand), C("Shape", cand)),
            Seq(Positive(C("m", actual)), Sp, Rightarrow, Sp,
                Both(C("Legal", policy, C("nil"), h), Both(Equal(actual, cand), Nonempty(cand)))),
            Equal(V("prior"), C("ofFintype", Seq(a, Sp, Mapsto, Sp, C("emb", C("mu", a))))),
            Equal(post, C("filter", V("prior"), actual)),
            Equal(C("support", post), cand),
            Implies(Member(a, cand), Equal(C("P", a), C("emb", Ratio(C("mu", a), C("m", cand))))),
            Implies(Seq(Neg, Sp, Member(a, cand)), Equal(C("P", a), D(0))),
            Implies(Nonempty(fiber), Both(Positive(C("m", fiber)),
                Equal(C("prob", post, response), C("emb", Ratio(C("m", fiber), C("m", cand)))))),
            Implies(Nonempty(fiber), Both(Positive(C("prob", post, response)),
                Equal(C("filter", post, response), C("filter", V("prior"), fiber)))),
            Implies(Member(a, fiber), Equal(C("filter", V("prior"), fiber, a), C("emb", Ratio(C("mu", a), C("m", fiber))))),
            Implies(Seq(Neg, Sp, Member(a, fiber)), Equal(C("filter", V("prior"), fiber, a), D(0)))
        ]));
    }
}
