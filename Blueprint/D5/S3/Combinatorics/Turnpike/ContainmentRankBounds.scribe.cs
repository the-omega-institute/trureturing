using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Turnpike;

internal sealed class ContainmentRankBoundsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Turnpike/ContainmentRankBounds";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The whole multiplicity block of every actually realized distance obeys the containment rank bounds.",
        H("Containment rank bounds for arbitrary real realizations"),
        Blocks(
            Paragraph(Text("This is a formalization of the known containment-based rank bounds of Elder, Marçais and Kingsford, WABI 2026, Lemma 14 and Appendix A.3, DOI 10.4230/LIPIcs.WABI.2026.20 (CC BY 4.0). The corresponding arXiv:2603.18283v1 statement is Lemma 13. Rank in the source is any occurrence index in the expanded decreasing distance multiset. Applying both endpoints of a used equal-value block gives the two bounds here. This makes no claim of mathematical novelty or resolution of an open problem.")),
            Paragraph(Text("All indices below are zero-based. Interval(n) is the subtype of pairs (i,j) in Fin(n) with i<j. For e=(i,j), set L(n,e)=(i.val+1)*(n-j.val) and U(n,e)=choose(n,2)-choose(j.val-i.val+1,2)+1, with natural subtraction. Set A(mu,q)=1+sum over r<q of mu(r) and B(mu,q)=sum over r<=q of mu(r). Delta(x,e)=x(j)-x(i). These definitions specify every abbreviation in the closed displayed formula.")),
            Describe.Lean(DescribeId.Create("turnpike-containment-rank-bounds"),
                DeclarationHandle.Create(Module + ".containment_rank_bounds"),
                H("Whole used blocks and original mask soundness"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGeometry/elder2026turnpike")),
                Blocks(
                    Paragraph(Text("Realizes(y,mu,x) is the existing predicate: x is strictly increasing; every interval difference equals some label y(q); and the cardinality of each entire interval fiber equals mu(q). The theorem assumes only this predicate, StrictAnti(y), and the displayed used-label equality. It quantifies over all natural n and d, all real y and x and all natural mu. There is no Admissible premise, n>=3 premise, positivity premise on every label, or positivity premise on every multiplicity. Unused bins may have zero multiplicity and negative values compatible with strict decrease. A used bin is positive by its inhabited fiber.")),
                    Paragraph(Text("The original RankAllowed(mu,e,q) is the intersection condition L(n,e)<=B(mu,q) and A(mu,q)<=U(n,e). The theorem proves the stronger whole-block inequalities L(n,e)<=A(mu,q) and B(mu,q)<=U(n,e), then derives the unchanged intersection predicate from positivity of the used multiplicity. It neither changes that predicate nor changes the rank mask or full/spine linear-programming objects.")),
                    Paragraph(Text("For each interval the proof chooses its unique label using Realizes and injectivity of strictly decreasing y. The existing Finset.sum_card_fiberwise_eq_card_filter identifies cumulative multiplicities with counts of intervals whose labels lie in the corresponding index range, including empty fibers. A true superinterval has strictly larger real difference; a true subinterval has strictly smaller real difference, by strict increase of x. The target interval itself supplies the one exceptional occurrence in each direction.")),
                    Paragraph(Text("The superinterval family is put in bijection with Iic(i) times Ici(j). The subinterval family is put in bijection with ordered pairs from Icc(i,j). Fin.card_Iic, Fin.card_Ici, Fin.card_Icc, Finset.card_product and Finset.card_product_filter_lt supply their generic cardinalities. The partition of all intervals into labels <=q and >q and the existing Fintype.card_product_filter_lt give the upper endpoint after natural arithmetic. These generic counting suppliers are reused, not claimed as new mathematics. The live new construction is the connection from geometric interval containment through real differences and unique labels to the multiplicity histogram.")),
                    Paragraph(Text("The generality includes two-point rulers and arbitrary translations and positive scalings of a realization. Labels with zero multiplicity do not affect the cumulative counts. For a two-point ruler with one used label and an unused negative label, both containment endpoints equal one. No LP integrality, completeness of pruning, or sufficiency of local marginals follows from this result."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula body = Imp(App(Q("StrictAnti"),V("y")),
            Imp(App(Q("Realizes"),V("y"),V("mu"),V("x")),
                Imp(Equal(App(Q("Delta"),V("x"),V("e")),App(V("y"),V("q"))),
                    And(Le(App(Q("L"),V("n"),V("e")),App(Q("A"),V("mu"),V("q"))),
                        And(Le(App(Q("B"),V("mu"),V("q")),App(Q("U"),V("n"),V("e"))),
                            App(Q("RankAllowed"),V("mu"),V("e"),V("q")))))));
        return All("n",Q("Nat"),All("d",Q("Nat"),
            All("y",Arrow(App(Q("Fin"),V("d")),Q("Real")),
            All("mu",Arrow(App(Q("Fin"),V("d")),Q("Nat")),
            All("x",Arrow(App(Q("Fin"),V("n")),Q("Real")),
            All("e",App(Q("Interval"),V("n")),All("q",App(Q("Fin"),V("d")),body)))))));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(Operatorname,Grp(F.Id(name)));
    private static Formula App(Formula f,params Formula[] args) => new Formula.Apply(f,[..args]);
    private static Formula Par(Formula f) => Seq(Left,Open,f,Right,Close);
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula All(string v,Formula t,Formula b) => Seq(Forall,Sp,Par(Seq(V(v),Colon,Sp,t)),Comma,Sp,Par(b));
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
}
