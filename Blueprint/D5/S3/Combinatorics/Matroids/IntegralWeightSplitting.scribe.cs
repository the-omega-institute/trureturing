using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class IntegralWeightSplittingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/IntegralWeightSplitting";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native matroids with a common base admit integral weight splitting with one base globally optimal for both summands.",
        H("Integral weight splitting for finite native matroids"),
        Blocks(
            Entry("weightSum", "integral-matroid-weight-sum", "Actual integral set weight", SumFormula(),
                "The sum is over the actual finite set B, using B.toFinite.toFinset. Weights are integers and may be negative, zero or tied.",
                DescribeRole.Definition),
            Entry("ExchangeArc", "integral-matroid-exchange-arc", "Tagged legal native exchanges", ArcFormula(),
                "An arc stores a tag t and elements b,e. It requires b in B, e in M1.E outside B, and insert e (B minus {b}) to be a base of M1 when t is true and of M2 when t is false. Under equal grounds this is exactly the two native exchange relations.",
                DescribeRole.Definition),
            Entry("exchangeGraph", "integral-matroid-exchange-graph", "The oriented tagged exchange graph", GraphFormula(),
                "For a true tag the source is b and the target is e; for a false tag the source is e and the target is b. Tags distinguish the two legal exchange types even when both occur for the same pair.",
                DescribeRole.Definition),
            Entry("exchangeWeight", "integral-matroid-exchange-weight", "Asymmetric integral arc weights", ArcWeightFormula(),
                "First-matroid arcs have weight zero. Second-matroid arcs have weight w(b)-w(e). Walk weight is the sum along the entire edge list, counting repeated edges and vertices with multiplicity.",
                DescribeRole.Definition),
            Entry("exchange_local_is_global_minimum", "integral-matroid-local-global", "Exchange inequalities imply global base optimality", LocalFormula(),
                "For any native finite matroid and any integral q, if a base B satisfies q(b)<=q(e) for every legal exchange with b in B and e in M.E outside B, then B has no larger actual q-sum than any base C. The proof establishes that B intersects every real lower threshold in a basis of that threshold and applies native_weighted_base_rank_saturation. An unsaturated threshold would admit an exchange removing b outside the threshold and inserting e inside it, contradicting the assumed exchange inequality.",
                DescribeRole.Theorem),
            Entry("optimal_common_base_closedWalk_nonpos", "integral-matroid-closed-walk", "Common-base minimality excludes every positive closed walk", ClosedWalkFormula(),
                "Let B be a common base minimizing the actual integral w-sum among all common bases. Every finite closed walk in the exact tagged exchange graph has nonpositive weight. This includes empty walks and walks with repetitions. The proof does not require toggling a cycle to preserve independence. For each tag, average the incidence vectors of its legal exchange bases, using B on edges carrying the other tag, and include one additional copy of B. The closed-walk balance identity makes the two averages identical. This common vector satisfies both native rank-inequality systems and has total coordinate sum equal to the base rank. Its w-cost is w(B) minus the walk weight divided by the edge-list length plus one. The maximum-cardinality face and its minimum-cost exposed face are compact; Krein-Milman supplies an extreme point. The existing intersection-polytope zero-one theorem applies after replacing each M by M restricted upward to univ, which preserves all ranks and adds only loops outside the native ground. The zero-one point has the same cardinality as B and yields an actual common base of no greater cost. Minimality of B therefore forces the walk weight to be nonpositive.",
                DescribeRole.Theorem),
            Entry("finite_integral_weight_splitting", "finite-integral-matroid-weight-splitting", "Full integral common-base splitting", MainFormula(),
                "For every universe u, finite carrier E, native matroids M1 and M2 with equal grounds and at least one common base, and integer weight w, there are a set B and integer functions c,d on all of E. The same B is a base of both matroids, c(e)+d(e)=w(e) for every carrier element, and B minimizes c among every M1-base and d among every M2-base. A minimum-w common base is selected internally from the finite nonempty family of all common bases. Closed-walk nonpositivity supplies an integer potential phi through Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos. Set c=phi and d=w-phi. The first arc inequality is c(b)<=c(e), while the second is phi(e)+w(b)-w(e)<=phi(b), equivalently d(b)<=d(e). Apply the local-to-global theorem twice. The split equality is pointwise on E, including elements outside the shared native ground.",
                DescribeRole.Theorem),
            Paragraph(Text(
                "The theorem includes empty carriers, empty and proper grounds, empty common bases, rank zero, loops, coloops, nonrepresentable matroids, and tied, negative, zero or arbitrary integral weights whenever the common-base premise holds. It assumes no optimum, splitting, dual prices, representation, algorithm or rank-profile certificate, and makes no algorithmic or complexity claim.")),
            Paragraph(Text(
                "This is a formalization of a published theorem. Frank, A Weighted Matroid Intersection Algorithm, Journal of Algorithms 2 (1981), 328-336, gives integral splitting for fixed-cardinality common independent sets (https://www.cs.elte.hu/~frank/cikkek/FrankJ6.PDF). Frank, Connections in Combinatorial Optimization, author-posted corrected OUP proof, Theorem 13.2.4 and Corollary 13.2.6, pp. 424-425, explicitly treat common bases (https://www.cs.elte.hu/~frank/cikkek/FrankB1.pdf). Those sources use maximum weights; negating weights gives the minimum convention here. The proof above uses the repository's existing primal intersection-polytope integrality and integer-potential suppliers. It is not an originality or open-problem-resolution claim, and does not assert a solution of the separate full joint-exchange event.")))));

    private static DocumentBlock.Describe Entry(string declaration, string id, string title, Formula statement,
        string explanation, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
        StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), role);

    private static Formula E => F.Id("E");
    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula SetE => Call("Set", E);
    private static Formula Weight => new Formula.TypeArrow(E, Z);
    private static Formula Base(Formula m, Formula b) => Call("Matroid.IsBase", m, b);
    private static Formula Total(Formula q, Formula b) => Call("weightSum", q, b);
    private static Formula Ground(Formula m) => Seq(m, Dot, F.Id("E"));
    private static Formula In(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Difference(Formula a, Formula b) => Seq(a, Sp, Setminus, Sp, b);
    private static Formula Singleton(Formula a) => Seq(OpenBrace, a, CloseBrace);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Exchange(Formula b, Formula x, Formula y) => Call("insert", y, Difference(b, Singleton(x)));
    private static Formula If(Formula p, Formula a, Formula b) =>
        Seq(Operatorname, Grp(F.Id("if")), Sp, p, Sp, Operatorname, Grp(F.Id("then")), Sp, a,
            Sp, Operatorname, Grp(F.Id("else")), Sp, b);
    private static Formula Universe(Formula body) => All("E", new Formula.Subscript(F.Id("Type"), F.Id("u")),
        Seq(OpenBracket, Call("Finite", E), CloseBracket, Comma, Sp, body));
    private static Formula Matroids(Formula body) => All("M1", Call("Matroid", E), All("M2", Call("Matroid", E), body));
    private static Formula Min(Formula m, Formula q, Formula b, string name) => All(name, SetE,
        Imp(Base(m, F.Id(name)), Leq(Total(q, b), Total(q, F.Id(name)))));

    private static Formula SumFormula()
    {
        Formula q = F.Id("q"), b = F.Id("B"), x = F.Id("e");
        Formula index = Seq(x, Sp, InMacro, Sp, Call("toFinite.toFinset", b));
        return Disp(Universe(All("q", Weight, All("B", SetE,
            Equal(Total(q, b), Seq(new Formula.Subscript(Sum, Grp(index)), Sp, Call("q", x)))))));
    }

    private static Formula ArcFormula()
    {
        Formula m1 = F.Id("M1"), m2 = F.Id("M2"), b = F.Id("B");
        Formula t = F.Id("t"), x = F.Id("b"), y = F.Id("e");
        Formula triples = Seq(Call("Bool"), Sp, Times, Sp, E, Sp, Times, Sp, E);
        Formula body = Seq(OpenBrace, Pair(t, Pair(x, y)), Sp, InMacro, Sp, triples,
            Sp, Mid, Sp, And(In(x, b), And(In(y, Difference(Ground(m1), b)),
                Base(If(Equal(t, F.Id("true")), m1, m2), Exchange(b, x, y)))), CloseBrace);
        return Disp(Universe(Matroids(All("B", SetE, Equal(Call("ExchangeArc", m1, m2, b), body)))));
    }

    private static Formula GraphFormula()
    {
        Formula m1 = F.Id("M1"), m2 = F.Id("M2"), b = F.Id("B"), a = F.Id("a");
        Formula graph = Call("exchangeGraph", m1, m2, b);
        Formula t = Seq(a, Dot, F.Id("val"), Dot, F.D(1));
        Formula x = Seq(a, Dot, F.Id("val"), Dot, F.D(2), Dot, F.D(1));
        Formula y = Seq(a, Dot, F.Id("val"), Dot, F.D(2), Dot, F.D(2));
        return Disp(Universe(Matroids(All("B", SetE, All("a", Call("ExchangeArc", m1, m2, b),
            And(Equal(Call("source", graph, a), If(Equal(t, F.Id("true")), x, y)),
                Equal(Call("target", graph, a), If(Equal(t, F.Id("true")), y, x))))))));
    }

    private static Formula ArcWeightFormula()
    {
        Formula m1 = F.Id("M1"), m2 = F.Id("M2"), b = F.Id("B"), a = F.Id("a"), w = F.Id("w");
        Formula t = Seq(a, Dot, F.Id("val"), Dot, F.D(1));
        Formula x = Seq(a, Dot, F.Id("val"), Dot, F.D(2), Dot, F.D(1));
        Formula y = Seq(a, Dot, F.Id("val"), Dot, F.D(2), Dot, F.D(2));
        return Disp(Universe(Matroids(All("B", SetE, All("w", Weight, All("a", Call("ExchangeArc", m1, m2, b),
            Equal(Call("exchangeWeight", m1, m2, b, w, a),
                If(Equal(t, F.Id("true")), F.D(0), Seq(Call("w", x), Sp, Minus, Sp, Call("w", y))))))))));
    }

    private static Formula LocalFormula()
    {
        Formula m = F.Id("M"), q = F.Id("q"), b = F.Id("B"), x = F.Id("b"), y = F.Id("e");
        Formula local = All("b", E, Imp(In(x, b), All("e", E,
            Imp(In(y, Difference(Ground(m), b)), Imp(Base(m, Exchange(b, x, y)), Leq(Call("q", x), Call("q", y)))))));
        return Disp(Universe(All("M", Call("Matroid", E), All("q", Weight, All("B", SetE,
            Imp(Base(m, b), Imp(local, Min(m, q, b, "C"))))))));
    }

    private static Formula ClosedWalkFormula()
    {
        Formula m1 = F.Id("M1"), m2 = F.Id("M2"), b = F.Id("B"), w = F.Id("w"), c = F.Id("C"), s = F.Id("s"), p = F.Id("p");
        Formula minimum = All("C", SetE, Imp(Base(m1, c), Imp(Base(m2, c), Leq(Total(w, b), Total(w, c)))));
        Formula conclusion = All("s", E, All("p", Call("EdgeGraph.Walk", Call("exchangeGraph", m1, m2, b), s, s),
            Leq(Call("MaxPlusPotential.walkWeight", Call("exchangeWeight", m1, m2, b, w), p), F.D(0))));
        return Disp(Universe(Matroids(Imp(Equal(Ground(m1), Ground(m2)), All("w", Weight, All("B", SetE,
            Imp(Base(m1, b), Imp(Base(m2, b), Imp(minimum, conclusion)))))))));
    }

    private static Formula MainFormula()
    {
        Formula m1 = F.Id("M1"), m2 = F.Id("M2"), w = F.Id("w"), b = F.Id("B"), c = F.Id("c"), d = F.Id("d"), x = F.Id("e");
        Formula common = Some("B", SetE, And(Base(m1, b), Base(m2, b)));
        Formula split = All("e", E, Equal(Seq(Call("c", x), Sp, Plus, Sp, Call("d", x)), Call("w", x)));
        Formula certificate = Some("B", SetE, Some("c", Weight, Some("d", Weight,
            And(Base(m1, b), And(Base(m2, b), And(split, And(Min(m1, c, b, "C"), Min(m2, d, b, "D"))))))));
        return Disp(Universe(Matroids(Imp(Equal(Ground(m1), Ground(m2)), Imp(common, All("w", Weight, certificate))))));
    }

    private static Formula Call(string name, params Formula[] args)
    {
        var pieces = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (pieces.Count > 0) pieces.Add(Dot);
            pieces.Add(Seq(Operatorname, Grp(F.Id(part))));
        }
        return new Formula.Apply(Seq([.. pieces]), [.. args]);
    }
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Par(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
