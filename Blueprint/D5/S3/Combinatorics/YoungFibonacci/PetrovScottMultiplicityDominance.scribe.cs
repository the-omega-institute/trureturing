using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.YoungFibonacci;

internal sealed class PetrovScottMultiplicityDominanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/petrovscott2026clone");
    private const string ClaimQuote = "The matrix 𝐍ₙ is upper triangular. Furthermore, if Nᵤ,ᵥ is nonzero then "
        + "u ⪰ v and ℎ(u)=ℎ(v), where ℎ(w) denotes the total hike, i.e., the number of 2’s appearing in a Fibonacci word w.";
    private const string SplitQuote = "Let κ = (κ₁, …, κₘ) be a composition of an integer n ≥ 1. "
        + "We associate with κ two auxiliary Fibonacci compositions of n, denoted A(κ) = (α₁, …, αₚ₊₁) "
        + "and B(κ) = (β₁, …, βₚ₊₁), where p = ⌊m/2⌋, defined as follows:";
    private const string GammaQuote = "For i ∈ {1, …, n}, let Γᵢ(π) denote the set of openers or transients "
        + "a < i such that i ≤ b, where b is the element succeeding a in the same block of π.";
    private const string RankQuote = "For i ∈ C(π) ∪ T(π), let γᵢ(π) be the position of the opener or transient "
        + "in Γᵢ(π) preceding i, where we list the elements Γᵢ(π) = {a₁ < … < aₖ} in increasing order.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibonacci multiplicity support has equal hike and prefix dominance.",
        H("Fibonacci Multiplicity Dominance"), Blocks(
            Node("YF", "Fibonacci words of fixed weight", WordFormula(),
                "A Fibonacci word w=w₁…wℓ is any binary word with letters wⱼ∈{1,2}. "
                + "The integer |w|≔w₁+…+wℓ=n is called the weight of the word w. "
                + "(Section 2.1, p. 12.) Words are List Nat, and weight is List.sum.", Literature()),
            Node("hike", "Total hike", HikeFormula(), ClaimQuote
                + " (Conjecture 8.22, p. 47.) List.count 2 counts the letters equal to two.", Literature()),
            Node("Fib", "From ribbon rows to words", FibFormula(),
                "The Fibonacci word in 𝕐𝔽ₙ corresponding to a Fibonacci composition ς = (ς₁, …, ςₚ) of n "
                + "is denoted Fib(ς). (Definition 8.10, pp. 42–43.) A single row gives only ones. "
                + "Otherwise the initial and final runs have row size minus one, and interior runs have row size minus two. "
                + "List indices start at zero; getElem! and headD zero also specify the values outside this domain.", Literature()),
            Node("splitA", "The first split composition", SplitFormula(false), SplitQuote
                + " (Definition 8.12, p. 43.) The cases m ≤ 2 and m = 3 are separate. "
                + "The coordinates use zero-based list indices. Nat.div is integer division and Nat.mod is remainder.", Literature()),
            Node("splitB", "The second split composition", SplitFormula(true), SplitQuote
                + " (Definition 8.12, p. 43.) The first coordinate sums exactly p odd-indexed source parts. "
                + "On positive compositions, (1 + sum) - p represents the integer expression 1 - p + sum. "
                + "For odd m ≥ 5 the printed formula need not preserve weight; the matrix below keeps only pairs of weight n. "
                + "Nat.div is integer division.", Literature()),
            Node("Arc", "Consecutive elements in a partition block", ArcFormula(),
                "An arc is drawn in the upper half-plane between i, j ∈ {1, …, n} whenever i precedes j. "
                + "(Section 8.1, p. 38.) The condition says that no element of the same block lies strictly between a and b. "
                + "Source labels are shifted down by one into Fin n; partitions are Finpartition of Finset.univ.", Literature()),
            Node("IsNoncrossing", "Noncrossing partitions", NoncrossingFormula(),
                "A set partition π ∈ Π(n) is said to be non-crossing if its arcs are pairwise non-crossing; "
                + "the set of non-crossing set partitions of n is denoted NC(n). (Section 8.1, p. 38.) "
                + "The forbidden strict order is a < c < b < d for two arcs.", Literature()),
            Node("Gamma", "Active left endpoints", GammaFormula(), GammaQuote
                + " (Section 8.1, p. 38.) The finite filter records the active arcs by their left endpoints.", Literature()),
            Node("gamma", "Predecessor position", RankFormula(), RankQuote
                + " (Section 8.1, p. 38.) The rank starts at one and is zero if no predecessor exists.", Literature()),
            Node("ell", "Visits to each level", StatisticFormula(false),
                "ℓₖ(π) ≔ #{1 ≤ i ≤ n : #Γᵢ(π)=k}, k ≥ 0. (Equation (8.1), p. 38.) "
                + "The cardinality is taken over Fin n.", Literature()),
            Node("g", "Predecessors at each rank", StatisticFormula(true),
                "gₘ(π) ≔ #{i ∈ C(π) ∪ T(π) : γᵢ(π)=m}, m ≥ 1. (Equation (8.1), p. 38.) "
                + "Having a predecessor is exactly being a closer or transient.", Literature()),
            Node("peak", "Maximum active level", PeakFormula(),
                "p = max{k : ℓₖ(π) > 0}. (Definition 8.16, p. 44.) "
                + "For n ≥ 1 this is the maximum cardinality of Gamma over Fin n. Finset.sup also specifies the empty case.", Literature()),
            Node("z", "The alternating composition", ZFormula(),
                "Let π ∈ NC(n) be a non-crossing set partition. Define z₁(π)=ℓ₀(π), z₂ₖ(π)=gₖ(π), "
                + "z₂ₖ₊₁(π)=ℓₖ(π)−gₖ(π), where 1 ≤ k ≤ p and where p = max{k : ℓₖ(π) > 0}. "
                + "(Definition 8.16, p. 44.) The final coordinate alone is deleted when ℓₚ(π)=gₚ(π).", Literature()),
            Node("multiplicity", "The partition multiplicity", MultiplicityFormula(),
                "N(κ) = #{π ∈ NC(n) : z(π) = κ}. (Corollary 8.20, p. 46.) "
                + "The cardinality is a finite filter of all set partitions.", Literature()),
            Node("matrixEntry", "The multiplicity matrix", MatrixFormula(),
                "For a pair of Fibonacci words u, v ∈ 𝕐𝔽ₙ, set Nᵤ,ᵥ = N(κ) if u = u(κ) and v = v(κ) "
                + "for some composition κ ∈ Comp(n). By Lemma 8.14, this composition is unique if it exists. "
                + "Otherwise, set Nᵤ,ᵥ = 0. (Definition 8.21, p. 47.) Classical.choose selects a matching Composition n; "
                + "its blocks are supplied to the partition count. Both matrix indices in the theorem have weight n.", Literature()),
            Node("Dominates", "Dominance by prefix sums", DominanceFormula(),
                "Recall from [Oka94] that u ⪰ v if u=u₁⋯uₚ and v=v₁⋯v_q in 𝕐𝔽ₙ, "
                + "and u₁+⋯+uₖ ≥ v₁+⋯+vₖ for all 1 ≤ k ≤ min(p,q). "
                + "(Section 8.5, p. 47.) List.take includes every common nonempty prefix.", Literature()),
            Node("claim", "Petrov–Scott Conjecture 8.22", Disp(Iff(F.Id("claim"), ClaimBody())),
                ClaimQuote + " (Conjecture 8.22, p. 47.) The descending lexicographic order is the order "
                + "221, 212, 2111, 122, 1211, 1121, 1112, 11111 shown in Figure 8. "
                + "The two sentences are encoded for every n ≥ 1 and every pair of words of weight n. "
                + "The printed splitB expression is retained; the weight-preserving correction is a separate question.", Literature()),
            Node("result", "Upper triangularity and dominance at every weight", Disp(ClaimBody()),
                "Equal numbers of split rows give equal hike. Enlarging the trailing runs reduces the number "
                + "of twos in every reversed prefix, independently of the initial runs. Equal weight and hike "
                + "give equal lengths and convert this to the required forward-prefix inequalities. "
                + "At the first different letter, dominance excludes the opposite descending lexicographic direction.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static AssessedProvenance Literature() => AssessedProvenance.FromLiterature(Source);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create("petrov-scott-multiplicity-" + (name == "Gamma" ? "active-set" : name.ToLowerInvariant())),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula WordFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), a = F.Id("a");
        return Disp(All([B("n", Nat()), B("w", Words())], Iff(Call("YF", n, w),
            And(All([B("a", Nat())], Implies(Member(a, w), Or(Equal(a, D(1)), Equal(a, D(2))))),
                Equal(App(Q("List", "sum"), w), n)))));
    }

    private static Formula HikeFormula() => Disp(All([B("w", Words())],
        Equal(Call("hike", F.Id("w")), App(Q("List", "count"), D(2), F.Id("w")))));

    private static Formula FibFormula()
    {
        Formula c = F.Id("c"), j = F.Id("j"), length = App(Q("List", "length"), c);
        Formula run = App(Q("List", "replicate"), Subtract(Index(c, Add(j, D(1))),
            If(Equal(Add(j, D(2)), length), D(1), D(2))), D(1));
        Formula rest = App(Q("List", "flatMap"), Lambda("j", Nat(), Append(List(D(2)), run)),
            App(Q("List", "range"), Subtract(length, D(1))));
        Formula head = App(Q("List", "headD"), c, D(0));
        return Disp(All([B("c", Words())], Equal(Call("Fib", c), If(Le(length, D(1)),
            App(Q("List", "replicate"), head, D(1)),
            Append(App(Q("List", "replicate"), Subtract(head, D(1)), D(1)), rest)))));
    }

    private static Formula SplitFormula(bool second)
    {
        Formula k = F.Id("k"), m = F.Id("m"), p = F.Id("p"), j = F.Id("j");
        Formula twice = Multiply(D(2), j), last = Subtract(Multiply(D(2), p), D(1));
        Formula middle = App(Q("List", "map"), Lambda("j", Nat(), second
            ? Add(D(1), Index(k, Add(twice, D(1))))
            : Add(Index(k, Add(twice, D(1))), Index(k, Add(twice, D(2))))),
            App(Q("List", "range"), Subtract(p, D(1))));
        Formula first = second ? Subtract(Add(D(1), App(Q("List", "sum"),
            App(Q("List", "map"), Lambda("j", Nat(), Index(k, twice)), App(Q("List", "range"), p)))), p)
            : Index(k, D(0));
        Formula final = second ? Index(k, last) : If(Equal(App(Q("Nat", "mod"), m, D(2)), D(0)),
            Index(k, last), Add(Index(k, last), Index(k, Multiply(D(2), p))));
        Formula three = second ? List(Add(Index(k, D(0)), Index(k, D(2))), Index(k, D(1)))
            : List(Index(k, D(0)), Add(Index(k, D(1)), Index(k, D(2))));
        Formula body = Let("m", App(Q("List", "length"), k),
            Let("p", App(Q("Nat", "div"), m, D(2)), If(Le(m, D(2)), k,
                If(Equal(m, D(3)), three, Append(Append(List(first), middle), List(final))))));
        return Disp(All([B("k", Words())], Equal(Call(second ? "splitB" : "splitA", k), body)));
    }

    private static Formula ArcFormula()
    {
        Formula n = F.Id("n"), pi = F.Id("pi"), a = F.Id("a"), b = F.Id("b"),
            block = F.Id("block"), c = F.Id("c");
        Formula body = And(Lt(a, b), ExistsMany([B("block", App(F.Id("Finset"), Fin(n)))],
            And(Member(block, App(Q("Finpartition", "parts"), pi)), And(Member(a, block),
                And(Member(b, block), All([B("c", Fin(n))], Implies(Member(c, block), Not(And(Lt(a, c), Lt(c, b))))))))));
        return Disp(All([B("n", Nat()), B("pi", Partitions(n)), B("a", Fin(n)), B("b", Fin(n))],
            Iff(Call("Arc", pi, a, b), body)));
    }

    private static Formula NoncrossingFormula()
    {
        Formula n = F.Id("n"), pi = F.Id("pi"), a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), d = F.Id("d");
        return Disp(All([B("n", Nat()), B("pi", Partitions(n))], Iff(Call("IsNoncrossing", pi),
            All([B("a", Fin(n)), B("b", Fin(n)), B("c", Fin(n)), B("d", Fin(n))],
                Implies(Call("Arc", pi, a, b), Implies(Call("Arc", pi, c, d),
                    Not(And(Lt(a, c), And(Lt(c, b), Lt(b, d))))))))));
    }

    private static Formula GammaFormula()
    {
        Formula n = F.Id("n"), pi = F.Id("pi"), i = F.Id("i"), a = F.Id("a"), b = F.Id("b");
        return Disp(All([B("n", Nat()), B("pi", Partitions(n)), B("i", Fin(n))],
            Equal(Call("Gamma", pi, i), Filter(Lambda("a", Fin(n), ExistsMany([B("b", Fin(n))],
                And(Call("Arc", pi, a, b), And(Lt(a, i), Le(i, b))))), Q("Finset", "univ")))));
    }

    private static Formula RankFormula()
    {
        Formula n = F.Id("n"), pi = F.Id("pi"), i = F.Id("i"), a = F.Id("a"), b = F.Id("b");
        return Disp(All([B("n", Nat()), B("pi", Partitions(n)), B("i", Fin(n))],
            Equal(Call("gamma", pi, i), Card(Filter(Lambda("a", Fin(n), ExistsMany([B("b", Fin(n))],
                And(Call("Arc", pi, b, i), Le(a, b)))), Call("Gamma", pi, i))))));
    }

    private static Formula StatisticFormula(bool closers)
    {
        Formula n = F.Id("n"), pi = F.Id("pi"), k = F.Id("k"), i = F.Id("i"), a = F.Id("a");
        Formula condition = closers ? And(ExistsMany([B("a", Fin(n))], Call("Arc", pi, a, i)),
            Equal(Call("gamma", pi, i), k)) : Equal(Card(Call("Gamma", pi, i)), k);
        return Disp(All([B("n", Nat()), B("pi", Partitions(n)), B("k", Nat())],
            Equal(Call(closers ? "g" : "ell", pi, k), Card(Filter(Lambda("i", Fin(n), condition), Q("Finset", "univ"))))));
    }

    private static Formula PeakFormula()
    {
        Formula n = F.Id("n"), pi = F.Id("pi"), i = F.Id("i");
        return Disp(All([B("n", Nat()), B("pi", Partitions(n))], Equal(Call("peak", pi),
            App(Q("Finset", "sup"), Q("Finset", "univ"), Lambda("i", Fin(n), Card(Call("Gamma", pi, i)))))));
    }

    private static Formula ZFormula()
    {
        Formula n = F.Id("n"), pi = F.Id("pi"), p = F.Id("p"), zs = F.Id("zs"), j = F.Id("j"), next = Add(j, D(1));
        Formula body = Let("p", Call("peak", pi), Let("zs", App(Q("List", "cons"), Call("ell", pi, D(0)),
            App(Q("List", "flatMap"), Lambda("j", Nat(), List(Call("g", pi, next),
                Subtract(Call("ell", pi, next), Call("g", pi, next)))), App(Q("List", "range"), p))),
            If(Equal(Call("ell", pi, p), Call("g", pi, p)), App(Q("List", "dropLast"), zs), zs)));
        return Disp(All([B("n", Nat()), B("pi", Partitions(n))], Equal(Call("z", pi), body)));
    }

    private static Formula MultiplicityFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), pi = F.Id("pi");
        return Disp(All([B("n", Nat()), B("k", Words())], Equal(Call("multiplicity", n, k),
            Card(Filter(Lambda("pi", Partitions(n), And(Call("IsNoncrossing", pi), Equal(Call("z", pi), k))), Q("Finset", "univ"))))));
    }

    private static Formula MatchingBody(Formula k, Formula u, Formula v) =>
        And(Equal(u, Call("Fib", Call("splitA", App(Q("Composition", "blocks"), k)))),
            Equal(v, Call("Fib", Call("splitB", App(Q("Composition", "blocks"), k)))));

    private static Formula MatrixFormula()
    {
        Formula n = F.Id("n"), u = F.Id("u"), v = F.Id("v"), k = F.Id("k"), h = F.Id("h");
        Formula condition = ExistsMany([B("k", App(F.Id("Composition"), n))], MatchingBody(k, u, v));
        Formula body = Parenthesized(Seq(F.Id("if"), Sp, h, Sp, Colon, Sp, condition, Sp, F.Id("then"), Sp,
            Call("multiplicity", n, App(Q("Composition", "blocks"), App(Q("Classical", "choose"), h))),
            Sp, F.Id("else"), Sp, D(0)));
        return Disp(All([B("n", Nat()), B("u", Words()), B("v", Words())], Equal(Call("matrixEntry", n, u, v), body)));
    }

    private static Formula DominanceFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v"), k = F.Id("k");
        return Disp(All([B("u", Words()), B("v", Words())], Iff(Call("Dominates", u, v),
            All([B("k", Nat())], Implies(Le(D(1), k), Implies(Le(k, Call("min", App(Q("List", "length"), u),
                App(Q("List", "length"), v))), Le(App(Q("List", "sum"), App(Q("List", "take"), k, v)),
                    App(Q("List", "sum"), App(Q("List", "take"), k, u)))))))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), u = F.Id("u"), v = F.Id("v"), a = F.Id("a"), b = F.Id("b");
        Formula lex = App(Q("List", "Lex"), Lambda("a", Nat(), Lambda("b", Nat(), Lt(b, a))), v, u);
        Formula entry = Call("matrixEntry", n, u, v);
        return All([B("n", Nat())], Implies(Le(D(1), n), All([B("u", Words()), B("v", Words())],
            Implies(Call("YF", n, u), Implies(Call("YF", n, v), And(Implies(lex, Equal(entry, D(0))),
                Implies(NotEqual(entry, D(0)), And(Call("Dominates", u, v), Equal(Call("hike", u), Call("hike", v))))))))));
    }

    private static Formula Nat() => F.Id("Nat");
    private static Formula Words() => App(F.Id("List"), Nat());
    private static Formula Fin(Formula n) => App(F.Id("Fin"), n);
    private static Formula Partitions(Formula n) => App(F.Id("Finpartition"),
        Parenthesized(Seq(Q("Finset", "univ"), Sp, Colon, Sp, App(F.Id("Finset"), Fin(n)))));
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula ExistsMany(Formula.BoundVariable[] variables, Formula body) => new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(F.Id(name), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Lambda(string name, Formula type, Formula body) => Parenthesized(Seq(F.Id("fun"), Sp,
        Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Let(string name, Formula value, Formula body) => Parenthesized(Seq(F.Id("let"), Sp,
        F.Id(name), Sp, Seq(Colon, Eq), Sp, value, Semi, Sp, body));
    private static Formula If(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(F.Id("if"), Sp,
        Parenthesized(condition), Sp, F.Id("then"), Sp, yes, Sp, F.Id("else"), Sp, no));
    private static Formula List(params Formula[] items) => Seq(OpenBracket,
        Seq(items.SelectMany((item, index) => index == 0 ? new[] { item } : new[] { Comma, Sp, item }).ToArray()), CloseBracket);
    private static Formula Index(Formula list, Formula index) => Seq(list, OpenBracket, index, CloseBracket, Bang);
    private static Formula Append(Formula a, Formula b) => App(Q("List", "append"), a, b);
    private static Formula Filter(Formula predicate, Formula set) => App(Q("Finset", "filter"), predicate, set);
    private static Formula Card(Formula set) => App(Q("Finset", "card"), set);
    private static Formula Member(Formula a, Formula set) => Seq(a, Sp, InMacro, Sp, set);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
