using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonStrictNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict normalized bounds for full conditioned polygon families",
        H("Two original families with independent conditioned totals"),
        Blocks(Describe.Lean(DescribeId.Create("polygon-strict-normalization"),
            DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonStrictNormalization.original_normalized_strict"),
            H("Two nonempty cross-intersecting families have normalized sum below one"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Fix an arbitrary natural n at least 14 and derive NeZero(n) from this inequality. The vertices are ZMod(n), ear(i) is the chord with endpoints i-1 and i+1, and EarCenters(T) is the complete set of centres of ears present in T. The arbitrary finite sets P,Q are disjoint, their union K has pairwise noncrossing ears, and their ordered cardinalities (p,q) are (2,2), (3,3), (2,4), or (4,2). There is no restriction on their cyclic placement.")),
                Paragraph(Text("WholeFiber(P,Q) is definitionally ConditionFiber(P,Q,empty,empty): every maximal noncrossing finite set T of actual internal diagonals with P contained in EarCenters(T) and Q disjoint from EarCenters(T). The empty observation imposes no further condition. Thus WholeFiber(Q,P) is a separate full conditioned type on the same polygon. A and B are arbitrary finite subfamilies of these respective types, and every T in A and U in B has a common ear in their full EarCenters sets. In the formula Natcard denotes Nat.card, card denotes Finset.card, and every division and addition in the conclusion takes place in Real.")),
                Paragraph(Text("For H contained in E_K, let w(R) be the real cast of Nat.card(ConditionFiber(P,Q,H,R)). When the ears centred in H are pairwise noncrossing, the actual conditioned trace flip injects the fibre with trace insert(h,R) into the fibre with trace R. Finite insertion induction gives w(S) at most w(R) whenever R is contained in S contained in H. This argument retains zero fibres and uses no positivity assumption on individual traces.")),
                Paragraph(Text("For every h in H, source_conditioned_witnesses supplies an actual member of the empty-trace fibre containing two distinct diagonals crossing ear(h). Every image of the singleton flip has at most one such chord, since all retained chords coexist with ear(h) in its input. That supplied fan lies outside the image, so w({h}) is strictly below w(empty). Integrality and antitonicity give w(R)+1 at most w(empty) for every nonempty R contained in H.")),
                Paragraph(Text("The complete fibres partition WholeFiber(P,Q) by T mapped to EarCenters(T) intersect H. Equiv.sigmaSubtypeFiberEquiv supplies the finite-fibre partition, with only the ConditionFiber subtype identification performed locally. Summing over every R contained in H gives exactly Nat.card(WholeFiber(P,Q)); the empty trace and every actual completion remain in this total.")),
                Paragraph(Text("On the finite distributive lattice of subsets of H, the proof applies the pinned Mathlib fkg inequality to the monotone functions w(bottom)-w and the indicator of a relatively upper family C. Subtracting one unit at bottom preserves antitonicity by the integer gap. Since C is nonempty and omits bottom, this yields mass(w,C)/sum(w) strictly below card(C)/card(powerset(H)). The positive whole-fibre total comes from source_conditioned_witnesses. The local signed-shift and bottom-subtraction helpers are consumed applications of fkg.")),
                Paragraph(Text("exists_original_terminal_compression supplies the same H for both original families and upper families C,D contained in powerset(H), with the original cardinalities bounded by the two respective weighted masses. Both upper families are nonempty and cross-intersecting. The complement map R mapped to H minus R injects D into a family disjoint from C, so card(C)+card(D) is at most card(powerset(H)). Apply the strict weighted comparison independently to P given Q and Q given P, add the bounds, and obtain the displayed strict inequality.")),
                Paragraph(Text("Application with the explicit Catalan denominators.")),
                Paragraph(Text("For the full B-37.2 application, retain all the hypotheses above but allow A or B to be empty. Define the integer function Npq as follows; Catalan(k) is the natural Catalan number, choose(q,j) is the binomial coefficient, and n-p-j-2 uses natural subtraction.")),
                Display(CountDefinition()),
                Paragraph(Text("The pairwise noncrossing hypothesis on K is exactly PolygonEarContraction.Compatible(K). Apply PolygonConditionalCounts.conditional_card first to P,Q and then separately to Q,P, using disjointness in the corresponding orientation. WholeFiber is the complete fibre with empty observation, so these applications give the two integer identities below. They do not identify the two denominators.")),
                Display(Counts()),
                Paragraph(Text("Apply PolygonConditionedFan.source_conditioned_witnesses in each orientation, swapping the ordered cardinality case and rewriting union_comm for the second. Its nonempty whole-fibre witness and positive Nat.card give Npq(n,p,q)>0 and Npq(n,q,p)>0 in Int. Casting each integer identity to Real gives separately Nat.card(WholeFiber(P,Q))=Npq(n,p,q) and Nat.card(WholeFiber(Q,P))=Npq(n,q,p), with both right sides positive and nonzero in Real. These are casts of two actual counts, not assumptions or a symmetry assertion.")),
                Paragraph(Text("For every actual T in WholeFiber(P,Q) and U in WholeFiber(Q,P), PolygonSimultaneousCompression.common_ears_eq_trace_inter supplies the full common-ear identity below. E_K is the set of centres outside K whose ears are compatible with every ear in K. The identity transports the full-ear cross-intersection premise to the common observation carrier without requiring intersection inside a selected six-ear set.")),
                Display(CommonEars()),
                Paragraph(Text("Write S for the following expression in Real, with the integer Npq values cast individually.")),
                Display(NormalizedDefinition()),
                Paragraph(Text("If A and B are both nonempty, apply original_normalized_strict and rewrite its two whole-fibre denominators by their own cast count identities. This gives S<1. If A is empty, S=card(B)/Npq(n,q,p); Finset.card_le_univ bounds card(B) by Fintype.card(WholeFiber(Q,P))=Nat.card(WholeFiber(Q,P)). Dividing by its positive real total gives S<=1. If B is empty, use the separate bound for A and Npq(n,p,q). If both are empty, S=0.")),
                Display(R(X("S"), Leq, D(1))),
                Paragraph(Text("Equality cannot occur with both families nonempty. With A empty, S=1 is equivalent, by positivity of Npq(n,q,p), to card(B)=Nat.card(WholeFiber(Q,P)); Fintype.card and Finset.eq_univ_of_card then give B=univ on its own whole fibre. Conversely B=univ has precisely that total, so S=1. With B empty the same reasoning uses Npq(n,p,q) and A=univ on WholeFiber(P,Q). Positive whole totals exclude the both-empty pair from equality. Thus the exact equality classification is:")),
                Display(Equality()),
                Paragraph(Text("This application includes all n at least 14, all four ordered size cases, arbitrary compatible placements, every actual completion, and separate counts in the two orientations. It is a consequence of the strict theorem, the original count and fan results, the common-ear identity, and finite-cardinality facts. No separate named upper-bound, equality, count, cast or final-application theorem is needed.")),
                Paragraph(Text("The result and its application do not assert an exact completion with EarCenters(T)=P, the n-p-3 degree or rank formula, or the stronger intermediate trace and rank formula chains. The strict argument uses the two-crossing fan and FKG comparison. It gives no equality between Npq(n,p,q) and Npq(n,q,p), and no general classification outside the four ordered cases. The polygon gap and its composition are repository derivations; the generic FKG, finite-cardinality and reindexing steps are applications of pinned Mathlib results."))),
            DescribeRole.Theorem)), []));

    private static DocumentBlock Display(Formula value) => new DocumentBlock.DisplayFormula(Disp(value));
    private static Formula X(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Operand(Formula f) => f is Formula.Bind ? Seq(Open, f, Close) : f;
    private static Formula R(Formula a, Formula op, Formula b) => Seq(Open, Operand(a), Sp, op, Sp, Operand(b), Close);
    private static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    private static Formula AndF(Formula a, Formula b) => R(a, Land, b);
    private static Formula OrF(Formula a, Formula b) => R(a, Lor, b);
    private static Formula EqF(Formula a, Formula b) => R(a, F.Eq, b);
    private static Formula Member(Formula a, Formula b) => R(a, InMacro, b);
    private static Formula Union(Formula a, Formula b) => R(a, Cup, b);
    private static Formula Inter(Formula a, Formula b) => C("inter", a, b);
    private static Formula DivF(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula AddF(Formula a, Formula b) => R(a, Plus, b);
    private static Formula SubF(Formula a, Formula b) => R(a, Minus, b);
    private static Formula Cast(Formula a, string type) => C(type, a);
    private static Formula Card(Formula a) => C("card", a);
    private static Formula Whole(Formula p, Formula q) => C("WholeFiber", p, q);
    private static Formula Npq(Formula p, Formula q) => C("Npq", X("n"), p, q);
    private static Formula Vertex => C("ZMod", X("n"));
    private static Formula Sets => C("Finset", Vertex);
    private static Formula Ears(Formula t) => C("EarCenters", C("val", t));
    private static Formula Compatible => All("i", Vertex, Imp(Member(X("i"), Union(X("P"), X("Q"))),
        All("j", Vertex, Imp(Member(X("j"), Union(X("P"), X("Q"))),
            Imp(R(X("i"), Neq, X("j")),
                Seq(Neg, C("Cross", C("ear", X("i")), C("ear", X("j")))))))));
    private static Formula SizeCase(byte p, byte q) => AndF(EqF(Card(X("P")), D(p)), EqF(Card(X("Q")), D(q)));
    private static Formula Cases => OrF(SizeCase(2,2), OrF(SizeCase(3,3), OrF(SizeCase(2,4), SizeCase(4,2))));
    private static Formula CrossFamilies => All("T", Whole(X("P"), X("Q")), Imp(Member(X("T"), X("A")),
        All("U", Whole(X("Q"), X("P")), Imp(Member(X("U"), X("B")),
            Seq(Neg, C("Disjoint", Ears(X("T")), Ears(X("U"))))))));
    private static Formula NativeSum => AddF(
        DivF(Cast(Card(X("A")), "Real"), Cast(C("Natcard", Whole(X("P"), X("Q"))), "Real")),
        DivF(Cast(Card(X("B")), "Real"), Cast(C("Natcard", Whole(X("Q"), X("P"))), "Real")));
    private static Formula Statement()
    {
        Formula body = R(NativeSum, Lt, D(1));
        body = Imp(C("Nonempty", X("B")), body);
        body = Imp(C("Nonempty", X("A")), body);
        body = Imp(CrossFamilies, body);
        body = All("B", C("Finset", Whole(X("Q"), X("P"))), body);
        body = All("A", C("Finset", Whole(X("P"), X("Q"))), body);
        body = Imp(Cases, body);
        body = Imp(Compatible, body);
        body = Imp(C("Disjoint", X("P"), X("Q")), body);
        body = All("P", Sets, All("Q", Sets, body));
        return All("n", X("Nat"), Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp,
            Imp(R(D(1,4), Leq, X("n")), body)));
    }
    private static Formula CountDefinition()
    {
        var j = X("j");
        var term = R(R(new Formula.Power(Seq(Open, Minus, D(1), Close), j),
            Cdot, Cast(C("choose", X("q"), j), "Int")),
            Cdot, Cast(C("Catalan", SubF(SubF(SubF(X("n"), X("p")), j), D(2))), "Int"));
        return All("n", X("Nat"), All("p", X("Nat"), All("q", X("Nat"),
            EqF(Npq(X("p"), X("q")),
                Seq(Sum, Sp, Underscore, Grp(j, InMacro, Sp, C("range", AddF(X("q"), D(1)))),
                    Sp, Open, term, Close)))));
    }
    private static Formula Counts() => AndF(
        EqF(Cast(C("Natcard", Whole(X("P"), X("Q"))), "Int"), Npq(X("p"), X("q"))),
        EqF(Cast(C("Natcard", Whole(X("Q"), X("P"))), "Int"), Npq(X("q"), X("p"))));
    private static Formula CommonEars() => EqF(Inter(Ears(X("T")), Ears(X("U"))),
        Inter(Inter(Ears(X("T")), C("EK", Union(X("P"), X("Q")))),
            Inter(Ears(X("U")), C("EK", Union(X("P"), X("Q"))))));
    private static Formula NormalizedDefinition() => EqF(X("S"), AddF(
        DivF(Cast(Card(X("A")), "Real"), Cast(Npq(X("p"), X("q")), "Real")),
        DivF(Cast(Card(X("B")), "Real"), Cast(Npq(X("q"), X("p")), "Real"))));
    private static Formula Equality() => R(EqF(X("S"), D(1)), F.Iff,
        OrF(AndF(EqF(X("A"), Emptyset), EqF(X("B"), C("univ", Whole(X("Q"), X("P"))))),
            AndF(EqF(X("B"), Emptyset), EqF(X("A"), C("univ", Whole(X("P"), X("Q")))))));
}
