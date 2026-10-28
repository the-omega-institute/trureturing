using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Saturation;

internal sealed class WangTianStrongSaturationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/wangtian2026strongsaturation");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula n => F.Id("n");
    private static Formula k => F.Id("k");
    private static Formula h => F.Id("h");
    private static Formula Hh => F.Id("H");
    private static Formula A => F.Id("A");
    private static Formula S => F.Id("S");
    private static Formula e => F.Id("e");
    private static Formula V => Call("Fin", n);
    private static Formula Arcs => Call("Arc", n);
    private static Formula Graph => Call("Digraph", n);
    private static Formula Vertices => Call("vertices", Hh);
    private static Formula Edges => Call("arcs", Hh);
    private static Formula Subsets => Call("Finset", V);
    private static Formula Arcsets => Call("Finset", Arcs);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unrestricted exact eventual formula for the maximum number of arcs in a saturated strict digraph fails at connectivity three and arbitrarily large odd orders.",
        H("Integrality obstruction to the exact Wang–Tian strong-digraph formula"),
        Blocks(
            Paragraph(Text("All graphs are finite strict directed graphs. Arcs are ordered pairs of distinct vertices; opposite arcs can both occur. A host arc set has the full vertex carrier Fin n. A subdigraph has its own vertex subset and an independent arc subset, and may retain isolated vertices. Named operations below denote the displayed definitions, with the ambient n inferred when it is implicit in Lean. The functions fst and snd project the underlying ordered pair of an arc; card is finite cardinality. The proof components of the minimum and maximum are included in their dependent types.")),
            Node("arc", "Permissible ordered arcs", "Arc", All("n", N,
                Equal(Arcs, Subtype("p", Seq(V, Sp, Times, Sp, V),
                    Ne(Call("fst", F.Id("p")), Call("snd", F.Id("p")))))),
                "Arc n is the subtype of Fin n x Fin n with unequal coordinates. Each ordered pair appears at most once in a finite arc set; reversing the pair gives a separate permissible arc."),
            Node("digraph", "Subdigraph records", "Digraph", All("n", N,
                Seq(Graph, Sp, Colon, Eq, Sp, OpenBrace,
                    Typed(F.Id("vertices"), Subsets), Semi, Sp,
                    Typed(F.Id("arcs"), Arcsets), Semi, Sp,
                    Typed(F.Id("endpoints"), EndpointLaw(F.Id("vertices"), F.Id("arcs"))), CloseBrace)),
                "Digraph n is the record with precisely the displayed three fields, including the endpoint proof. There is no induced-subgraph requirement: deleting extra arcs or retaining isolated vertices is allowed. The field names in the record signature bind its subsequent field types."),
            Node("vertices", "The vertex field", "vertices", OnGraph(Typed(Vertices, Subsets)),
                "The vertex field is any finite subset of Fin n. It need not be the endpoints of the arc field."),
            Node("arcs", "The arc field", "arcs", OnGraph(Typed(Edges, Arcsets)),
                "The arc field is a finite set of permissible directed arcs whose endpoints satisfy the next field."),
            Node("endpoints", "The endpoint proof field", "endpoints", OnGraph(EndpointLaw(Vertices, Edges)),
                "For each arc in the record, both coordinates belong to its vertex set. This proof field is part of the structure, rather than an additional graph axiom."),
            Node("adj", "Directed adjacency", "Adj", OnGraph(All("a", V, All("b", V,
                Iff(Call("Adj", Hh, F.Id("a"), F.Id("b")), Ex("e", Arcs,
                    And(Member(e, Edges), Equal(Call("val", e), Pair(F.Id("a"), F.Id("b"))))))))),
                "Adjacency means that an arc in H has exactly the given ordered endpoints."),
            Node("dipath", "Vertex-simple directed paths", "Dipath", DipathFormula(),
                "The nonempty list a::l has no repeated vertices, every vertex lies in H.vertices, consecutive vertices satisfy H.Adj in the listed direction, and its final vertex is b. The getLast proof argument is the canonical proof that a cons list is nonempty; it contributes no additional condition."),
            Node("strong", "Strong connectivity", "Strong", OnGraph(Iff(Call("Strong", Hh),
                All("a", V, Imp(Member(F.Id("a"), Vertices), All("b", V,
                    Imp(Member(F.Id("b"), Vertices), Imp(Ne(F.Id("a"), F.Id("b")),
                        Call("Dipath", Hh, F.Id("a"), F.Id("b"))))))))),
                "Quantifying ordered distinct endpoints requires paths in both directions. The predicate is vacuous on empty and singleton records; positive strong connectivity below explicitly excludes the empty record."),
            Node("delete", "Vertex deletion", "delete", OnGraph(All("S", Subsets,
                And(Equal(Call("vertices", Call("delete", Hh, S)), Seq(Vertices, Sp, Setminus, Sp, S)),
                    Equal(Call("arcs", Call("delete", Hh, S)), Filter("e", Arcs, Edges,
                        And(Not(Member(Call("fst", Call("val", e)), S)), Not(Member(Call("snd", Call("val", e)), S)))))))),
                "Deletion restricts the original vertices and arcs. Its endpoint proof follows from H.endpoints and the two nonmembership conditions, so the result is again a Digraph n. The difference is finite-set difference, not arithmetic subtraction."),
            Node("separator", "Separators, including trivial remainders", "Separator", OnGraph(All("S", Subsets,
                Iff(Call("Separator", Hh, S), And(Subset(S, Vertices),
                    Or(Not(Call("Strong", Call("delete", Hh, S))),
                        Equal(Card(Call("vertices", Call("delete", Hh, S))), D(1))))))),
                "A separator is a subset of the original vertices whose deletion leaves a graph that is not strongly connected or has exactly one vertex. Trivial means singleton. Removing all vertices does not count via the singleton alternative."),
            Node("separator-cards", "The actual finite separator-size family", "separatorCards", OnGraph(
                Equal(Call("separatorCards", Hh), Call("image", F.Id("card"),
                    Filter("S", Subsets, Call("powerset", Vertices), Call("Separator", Hh, S))))),
                "Take every subset of H.vertices, keep exactly the separators, then take their cardinalities. If H is nonempty, erasing one chosen vertex from H.vertices leaves a singleton and supplies a member of this family."),
            Node("connectivity", "An attained minimum with its full certificate", "connectivity", ConnectivityFormula(),
                "Nonempty T means there exists a vertex in T. The value is min' of separatorCards, with its nonemptiness proof supplied by the singleton remainder. The subtype retains an actual minimizing separator and the inequality against every separator. The displayed value equation uses min' only on this proved nonempty family; there is no default for an empty family."),
            Node("kstrong", "Positive strong connectivity and the empty-domain convention", "KStrong", All("n", N, All("k", N, All("H", Graph,
                Iff(Call("KStrong", k, Hh), ProofEx("h", Call("Nonempty", Vertices),
                    Leq(k, Call("val", Call("connectivity", Hh, h)))))))),
                "The existential h is a proof of vertex nonemptiness. Thus even a vacuously strongly connected empty record is excluded. The minimum certificate applied to the singleton remainder gives k+1 <= card(H.vertices) whenever KStrong k H. This matches the size consequence used in the source's Lemma 2.2."),
            Node("forbidden", "Arbitrary forbidden subdigraphs", "Forbidden", OnArcset(
                Iff(Call("Forbidden", k, A), Ex("H", Graph,
                    And(Subset(Edges, A), Call("KStrong", k, Hh))))),
                "The quantified record H chooses both a vertex subset and an arc subset. Its endpoint field puts all its arcs on those vertices. Inclusion in the full host A imposes neither spanning nor induced containment."),
            Node("free", "Forbidden-free hosts", "Free", OnArcset(Iff(Call("Free", k, A), Not(Call("Forbidden", k, A)))),
                "A host is free precisely when no arbitrary subdigraph is k-strong."),
            Node("saturated", "Every missing permissible arc creates a forbidden subdigraph", "Saturated", OnArcset(
                Iff(Call("Saturated", k, A), And(Call("Free", k, A), All("e", Arcs,
                    Imp(Not(Member(e, A)), Call("Forbidden", k, Call("insert", e, A))))))),
                "Saturation includes freeness and quantifies every missing ordered arc. A reverse arc is tested independently even when its opposite is already present."),
            Node("family", "The finite family of all saturated hosts", "saturatedFamily", All("k", N, All("n", N,
                Equal(Call("saturatedFamily", k, n), Filter("A", Arcsets,
                    Call("powerset", Call("univ", Arcs)), Call("Saturated", k, A))))),
                "For positive k the empty arc set is free: a k-strong forbidden record would have at least two vertices, while empty adjacency cannot connect distinct vertices. Maximizing cardinality among all free arc sets gives a saturated set, because inserting a missing arc strictly increases cardinality. If n <= k, every graph is free and the complete arc set is saturated, including n=0. Hence the displayed finite saturated family is nonempty for every positive k and every n."),
            Node("extremum", "The actual attained extremal arc number", "extremum", ExtremumFormula(),
                "Let C be the image of card on saturatedFamily k n. It is finite and nonempty by the preceding maximal-free construction. The value of extremum is C.max'. Its subtype contains an actual saturated host attaining that value and domination over every saturated host. Nonempty refers to the family of hosts, not a requirement that n be positive; the full eventual claim and its contradicting witnesses use positive orders."),
            Node("claim", "The full unrestricted eventual equality", "claim", Equal(F.Id("claim"), ClaimBody()),
                "This is the complete positive-k reading of Conjecture 1 in Section 4, printed PDF page 13 of arXiv:2605.01269v1. The threshold may depend on k. The symbol hk is the proof of 1 <= k required by the actual extremum definition. All casts, divisions and subtractions in the equality are rational; choose is the natural binomial coefficient before casting. The printed conjecture has no floor, ceiling, divisibility restriction or error term. The refutation also applies to the local k >= 2 reading because it uses k=3."),
            Describe.Lean(DescribeId.Create("wt-result"), DeclarationHandle.Create(Prefix + "result"),
                H("No threshold satisfies the full exact formula"), StatementSource.FromAuthor(Disp(Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Assume the whole claim and use k=3. For any threshold N choose n=2N+5, which is at least N and at least five. Clearing denominator two in the rational equality gives 2 ex = 2 choose(2N+5,2) + 5(2N+3) = 2(choose(2N+5,2)+5N+7)+1. Both ex and choose are natural numbers. Injectivity of the natural-to-rational cast therefore equates an even natural with an odd natural, a contradiction. No value of an extremizer is assumed or calculated.")),
                    Paragraph(Text("This repository-derived argument concerns the literal exact unrestricted formula. It does not determine a corrected divisible-order, rounded, upper-bound or asymptotic statement. The source's construction theorem and other bounds are not assumed as axioms. The source note distinguishes the new conjecture from the related undirected Mader upper-bound literature; no global priority assertion is made."))), DescribeRole.Theorem),
            Paragraph(Text("For an arbitrary n-element finite vertex carrier W and a bijection f:W -> Fin n, send an ordered arc (u,v) to (f(u),f(v)). Injectivity preserves unequal endpoints, and the inverse bijection gives the inverse arc map. Map vertex subsets and arc subsets by these bijections; endpoint membership, arbitrary containment, insertion of a missing arc and cardinality are preserved. Map every vertex in a path list by f: list membership, nonrepetition, directed consecutive adjacency and the final endpoint are preserved, with the inverse list map proving the converse. Images under f commute with vertex-set difference, and the corresponding arc filter is exactly deletion of both endpoints. Thus the not-strong and singleton alternatives for separators correspond, and separator cardinalities and their attained minimum agree. The empty vertex set remains empty. Consequently forbiddenness, freeness and saturation correspond in both directions, and the sets of saturated arc counts, including their attained maximum, agree. This explains the labelled presentation at the definition level. No separate Lean transport theorem between two graph APIs is asserted; all formal objects here are directly on Fin n.")))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("wt-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula ProofAll(string name, Formula proposition, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Typed(F.Id(name), proposition)), Comma, Sp, body);
    private static Formula ProofEx(string name, Formula proposition, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Typed(F.Id(name), proposition)), Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula Card(Formula a) => Call("card", a);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Subtype(string variable, Formula type, Formula predicate) =>
        Seq(OpenBrace, Typed(F.Id(variable), type), Sp, Bar, Sp, predicate, CloseBrace);
    private static Formula Filter(string variable, Formula type, Formula set, Formula predicate) =>
        Seq(OpenBrace, Typed(F.Id(variable), type), Sp, Bar, Sp, And(Member(F.Id(variable), set), predicate), CloseBrace);
    private static Formula OnGraph(Formula body) => All("n", N, All("H", Graph, body));
    private static Formula OnArcset(Formula body) => All("n", N, All("k", N, All("A", Arcsets, body)));
    private static Formula EndpointLaw(Formula vertices, Formula arcs) => All("e", Arcs,
        Imp(Member(e, arcs), And(Member(Call("fst", Call("val", e)), vertices), Member(Call("snd", Call("val", e)), vertices))));
    private static Formula DipathFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), l = F.Id("l"), path = Call("cons", a, l), v = F.Id("v");
        return OnGraph(All("a", V, All("b", V, Iff(Call("Dipath", Hh, a, b), Ex("l", Call("List", V),
            And(Call("Nodup", path), And(All("v", V, Imp(Member(v, path), Member(v, Vertices))),
                And(Call("IsChain", Call("Adj", Hh), path), Equal(Call("getLast", path), b)))))))));
    }
    private static Formula ConnectivityFormula()
    {
        Formula m = F.Id("m"), c = Call("connectivity", Hh, h);
        Formula certificate = And(Ex("S", Subsets, And(Call("Separator", Hh, S), Equal(Card(S), m))),
            All("S", Subsets, Imp(Call("Separator", Hh, S), Leq(m, Card(S)))));
        return OnGraph(ProofAll("h", Call("Nonempty", Vertices), new Formula.Aligned([
            Typed(c, Subtype("m", N, certificate)),
            Equal(Call("val", c), Call("minPrime", Call("separatorCards", Hh)))])));
    }
    private static Formula ExtremumFormula()
    {
        Formula hk = F.Id("hk"), m = F.Id("m"), b = F.Id("B"), c = Call("extremum", k, n, hk);
        Formula certificate = And(Ex("A", Arcsets, And(Call("Saturated", k, A), Equal(Card(A), m))),
            All("B", Arcsets, Imp(Call("Saturated", k, b), Leq(Card(b), m))));
        return All("k", N, All("n", N, ProofAll("hk", Leq(D(1), k), new Formula.Aligned([
            Typed(c, Subtype("m", N, certificate)),
            Equal(Call("val", c), Call("maxPrime", Call("image", F.Id("card"), Call("saturatedFamily", k, n))))]))));
    }
    private static Formula ClaimBody()
    {
        Formula hk = F.Id("hk"), threshold = F.Id("N");
        Formula value = Rational(Call("val", Call("extremum", k, n, hk)));
        Formula rhs = Add(Mul(Mul(new Formula.Fraction(D(3), D(2)),
            Parenthesized(Sub(Rational(k), new Formula.Fraction(D(4), D(3))))),
            Parenthesized(Add(Sub(Rational(n), Rational(k)), D(1)))), Rational(Call("choose", n, D(2))));
        return All("k", N, ProofAll("hk", Leq(D(1), k), Ex("N", N, All("n", N,
            Imp(Leq(threshold, n), Equal(value, rhs))))));
    }
    private static Formula Rational(Formula value) => Parenthesized(Typed(value, Q));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
