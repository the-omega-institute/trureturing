using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class AdamsonFlahertyPotapovSpirakisTwoSwapGreedyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/adamsonflahertypotapovspirakis2024twoswap");
    private const string Conjecture = "Section 5, page 23: ‘For the 2-swap graph specifically, we leave open the problem of determining the shortest path between two given words w and v. We conjecture that the simple greedy algorithm used to derive the upper bound in Lemma 4 can be used to find the shortest path between any pair of vertices.’";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary words at distance one force arbitrarily many greedy swaps.",
        H("The 2-swap greedy shortest-path conjecture is false"),
        Blocks(
            Paragraph(Text("Words are functions Fin n → α. The paper's positions 1,…,n and alphabet 1,…,σ become zero-based finite types. A stage pairs occurrences in increasing position order before applying any of its swaps. Only unequal index pairs contribute to the length; this counts pairs even if a later application would exchange equal letters. The proposition below asks only for equality of this count with graph distance, and allows every maximal-count reference letter and every non-increasing order of the remaining letters.")),
            Node("twoSwap", "Exchanging two positions", TwoSwap(),
                "Definition 1, page 4: ‘Given a word w∈Σⁿ and pair i,j∈[n], i<j such that w[i]≠w[j], the 2-swap of w by (i,j), denoted w∘(i,j), returns the word w[1,i−1]w[j]w[i+1,j−1]w[i]w[j+1,n].’ Precomposition by Equiv.swap exchanges those entries; the restrictions on indices and letters appear in IsTwoSwapOf.", AssessedProvenance.FromLiterature(Source)),
            Node("parikh", "Counting each letter", Parikh(),
                "Page 4: ‘Given a word w∈Σⁿ, the Parikh vector of w, denoted P(w) is the σ-length vector such that the ith entry of P(w) contains the number of occurrences of symbol i in w, formally, for i∈[σ], P(w)[i]=|{j∈[n] | w[j]=i}|, where n=|w|.’ The finite-set cardinality counts each position once.", AssessedProvenance.FromLiterature(Source)),
            Node("IsTwoSwapOf", "The 2-swap relation", SwapRelation(),
                "Definition 1, page 4: ‘Given a word w∈Σⁿ and pair i,j∈[n], i<j such that w[i]≠w[j], the 2-swap of w by (i,j), denoted w∘(i,j), returns the word w[1,i−1]w[j]w[i+1,j−1]w[i]w[j+1,n].’ This predicate supplies precisely the two restrictions and the resulting word.", AssessedProvenance.FromLiterature(Source)),
            Node("swapGraph", "The graph on all words", SwapGraph(),
                "The graph SimpleGraph.fromRel makes the 2-swap relation undirected and excludes loops. Its vertices here are all functions Fin n → α.", AssessedProvenance.FromRepo(Source)),
            Node("configGraph", "The configuration graph", ConfigGraph(),
                "Page 5: ‘For a given alphabet Σ and Parikh vector P, the configuration graph of Σ∗|P is the undirected graph G(P)={V(P),E(P)} where:’ The source explains: ‘Informally, the configuration graph for a given Parikh vector P is the graph with each vertex corresponding to some word in Σ∗|P, and each edge connecting every pair of words w,u∈Σ∗|P such that there exists some 2-swap transforming w into u.’ SimpleGraph.induce restricts swapGraph to exactly these words.", AssessedProvenance.FromLiterature(Source)),
            Node("occurrences", "Occurrence positions in increasing order", Occurrences(),
                "Algorithm 1, page 9: ‘i ← index of kᵗʰ occurrence of x in w’. Filtering List.finRange n by equality to x lists exactly those positions in increasing order. The source's kᵗʰ occurrence has list index k−1.", AssessedProvenance.FromLiterature(Source)),
            Node("stageSwaps", "Pairing corresponding occurrences", StageSwaps(),
                "Algorithm 1, page 9: ‘i ← index of kᵗʰ occurrence of x in w’ and ‘j ← index of kᵗʰ occurrence of x in v’. List.zip pairs corresponding entries of the two occurrence lists. For equal Parikh vectors their lengths agree.", AssessedProvenance.FromLiterature(Source)),
            Node("applySwaps", "Applying a stage", ApplySwaps(),
                "Algorithm 1, page 9: ‘Apply all 2-swaps in S to w and set S ← ∅’. List.foldl applies them in increasing occurrence order. The length comparison below does not assume that this application reaches the target word.", AssessedProvenance.FromLiterature(Source)),
            Node("greedySwaps", "The sequence of stages", GreedySwaps(),
                "Algorithm 1, page 9: ‘for x ∈ Σ \\ {1} do’. The empty list performs no stage. A nonempty list first records the occurrence pairs for its head letter, then continues from the word obtained by applying those pairs.", AssessedProvenance.FromLiterature(Source)),
            Node("greedyLength", "Counting nontrivial pairs", GreedyLength(),
                "A nontrivial pair has distinct position indices. Filtering by that predicate and taking List.length gives the count compared with SimpleGraph.dist. Pairs are counted before imposing any condition on the letters when the pair is eventually applied.", AssessedProvenance.FromRepo(Source)),
            Node("AdmissibleOrder", "Permitted reference letters and orders", AdmissibleOrder(),
                "Proof of Lemma 4, page 9: ‘We assume, without loss of generality, that P[1]≥P[2]≥⋯≥P[σ].’ Algorithm 1 runs over Σ \\ {1}. The existential reference letter has maximal count. The list has no duplicates, omits that letter, contains every other letter, and has non-increasing counts. Thus all choices among ties are included.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The shortest-path conjecture", Equal(Id("claim"), Parenthesized(ClaimBody())),
                Conjecture + " The formula permits any alphabet size σ and word length n, any two words with the same Parikh vector, and any permitted letter order. The proof h puts the target word in the same configuration graph. It asks only for equality of the count with the distance; reaching the target and legality of every generated pair are additional requirements of a path.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation by an unbounded binary family"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For each k≥2, take w=0ᵏ1ᵏ and v=1·0ᵏ⁻¹·1ᵏ⁻¹·0. Each letter occurs k times in both words. Exchanging positions 0 and 2k−1 turns w into v, so their distance is one. Pairing the zero occurrences moves every occurrence, and pairing the one occurrences also moves every occurrence: either permitted binary order therefore generates k nontrivial pairs. This proves failure throughout an unbounded family; k=2 contradicts the quantified proposition. The argument determines neither a shortest-path algorithm for unrestricted alphabets nor its complexity."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("adamson-flaherty-potapov-spirakis-2023-two-swap-greedy"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(DescribeId.Create(name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(F.Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula FinN => Call("Fin", Id("n"));
    private static Formula Word => new Formula.TypeArrow(FinN, Id("A"));
    private static Formula Pair => F.Seq(FinN, F.Times, FinN);
    private static Formula Pairs => Call("List", Parenthesized(Pair));
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula Qualified(string owner, string name) =>
        F.Seq(F.Operatorname, F.Grp(F.Id(owner)), F.Dot, F.Operatorname, F.Grp(F.Id(name)));
    private static Formula Up(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        F.Seq(Id("fun"), Parenthesized(F.Seq(Id(name), F.Colon, type)), F.Mapsto, F.Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Proj(Formula pair, int index) => F.Seq(pair, F.Dot, Num(index));
    private static Formula Empty => F.Seq(F.OpenBracket, F.CloseBracket);
    private static Formula Parameters(Formula body, bool decidable = true, bool finite = false)
    {
        var result = All("n", N, body);
        if (finite) result = F.Seq(F.OpenBracket, Call("Fintype", Id("A")), F.CloseBracket, F.Comma, result);
        if (decidable) result = F.Seq(F.OpenBracket, Call("DecidableEq", Id("A")), F.CloseBracket, F.Comma, result);
        return All("A", Id("Type"), result);
    }
    private static Formula SetOf(string name, Formula body) =>
        F.Seq(F.OpenBrace, Id(name), F.Mid, body, F.CloseBrace);
    private static Formula Vertex(string word, Formula proof) =>
        F.Seq(F.Langle, F.Sp, Id(word), F.Comma, proof, F.Rangle);

    private static Formula TwoSwap() => Parameters(All("w", Word, All("i", FinN, All("j", FinN,
        Equal(Call("twoSwap", Id("w"), Id("i"), Id("j")),
            F.Seq(Id("w"), F.Circ, Up("Equiv", "swap", Id("i"), Id("j"))))))), decidable: false);
    private static Formula Parikh() => Parameters(All("w", Word, All("a", Id("A"),
        Equal(Call("parikh", Id("w"), Id("a")), Up("Finset", "card",
            Up("Finset", "filter", Lam("j", FinN, Equal(Call("w", Id("j")), Id("a"))), Qualified("Finset", "univ")))))));
    private static Formula SwapRelation() => Parameters(All("w", Word, All("v", Word,
        Equal(Call("IsTwoSwapOf", Id("w"), Id("v")), Parenthesized(
            Exists("i", FinN, Exists("j", FinN, And(Lt(Id("i"), Id("j")),
                And(NotEqual(Call("w", Id("i")), Call("w", Id("j"))),
                    Equal(Id("v"), Call("twoSwap", Id("w"), Id("i"), Id("j"))))))))))));
    private static Formula SwapGraph() => Parameters(Equal(Call("swapGraph", Id("n"), Id("A")),
        Up("SimpleGraph", "fromRel", Id("IsTwoSwapOf"))));
    private static Formula ConfigGraph() => Parameters(All("P", new Formula.TypeArrow(Id("A"), N),
        Equal(Call("configGraph", Id("P")), F.Seq(
            Call("swapGraph", Id("n"), Id("A")), F.Dot, F.Operatorname, F.Grp(F.Id("induce")),
            Parenthesized(SetOf("w", Equal(Call("parikh", Id("w")), Id("P"))))))));
    private static Formula Occurrences() => Parameters(All("w", Word, All("x", Id("A"),
        Equal(Call("occurrences", Id("w"), Id("x")), Up("List", "filter",
            Lam("i", FinN, Call("decide", Parenthesized(Equal(Call("w", Id("i")), Id("x"))))),
            Up("List", "finRange", Id("n")))))));
    private static Formula StageSwaps() => Parameters(All("u", Word, All("v", Word, All("x", Id("A"),
        Equal(Call("stageSwaps", Id("u"), Id("v"), Id("x")), Up("List", "zip",
            Call("occurrences", Id("u"), Id("x")), Call("occurrences", Id("v"), Id("x"))))))));
    private static Formula ApplySwaps() => Parameters(All("u", Word, All("S", Pairs,
        Equal(Call("applySwaps", Id("u"), Id("S")), Up("List", "foldl",
            Lam("c", Word, Lam("p", Pair, F.Seq(Id("c"), F.Circ,
                Up("Equiv", "swap", Proj(Id("p"), 1), Proj(Id("p"), 2))))), Id("u"), Id("S"))))), decidable: false);
    private static Formula GreedySwaps()
    {
        var stage = Call("stageSwaps", Id("u"), Id("v"), Id("x"));
        var cons = F.Seq(Id("x"), F.Colon, F.Colon, Id("t"));
        var first = All("u", Word, Equal(Call("greedySwaps", Id("v"), Empty, Id("u")), Empty));
        var next = All("x", Id("A"), All("t", Call("List", Id("A")), All("u", Word,
            Equal(Call("greedySwaps", Id("v"), Parenthesized(cons), Id("u")),
                Up("List", "append", stage, Call("greedySwaps", Id("v"), Id("t"),
                    Call("applySwaps", Id("u"), stage)))))));
        return Parameters(All("v", Word, new Formula.Aligned([first, next])));
    }
    private static Formula GreedyLength() => Parameters(All("o", Call("List", Id("A")),
        All("w", Word, All("v", Word, Equal(Call("greedyLength", Id("o"), Id("w"), Id("v")),
            Up("List", "length", Up("List", "filter",
                Lam("p", Pair, Call("decide", Parenthesized(NotEqual(Proj(Id("p"), 1), Proj(Id("p"), 2))))),
                Call("greedySwaps", Id("v"), Id("o"), Id("w")))))))));
    private static Formula AdmissibleOrder()
    {
        var refLetter = Id("r"); var order = Id("o");
        var counts = All("a", Id("A"), Le(Call("parikh", Id("w"), Id("a")), Call("parikh", Id("w"), refLetter)));
        var others = All("a", Id("A"), Imp(NotEqual(Id("a"), refLetter), Mem(Id("a"), order)));
        var sorted = Up("List", "Pairwise", Lam("a", Id("A"), Lam("b", Id("A"),
            Le(Call("parikh", Id("w"), Id("b")), Call("parikh", Id("w"), Id("a"))))), order);
        var body = Exists("r", Id("A"), And(counts, And(Up("List", "Nodup", order),
            And(new Formula.Not(Parenthesized(Mem(refLetter, order))), And(others, sorted)))));
        return Parameters(All("w", Word, All("o", Call("List", Id("A")),
            Equal(Call("AdmissibleOrder", Id("w"), order), Parenthesized(body)))), finite: true);
    }
    private static Formula ClaimBody()
    {
        var words = new Formula.TypeArrow(Call("Fin", Id("n")), Call("Fin", Id("s")));
        var distance = Up("SimpleGraph", "dist", Call("configGraph", Call("parikh", Id("w"))),
            Vertex("w", Id("rfl")), Vertex("v", Id("h")));
        var conclusion = Exists("o", Call("List", Call("Fin", Id("s"))),
            And(Call("AdmissibleOrder", Id("w"), Id("o")),
                Equal(Call("greedyLength", Id("o"), Id("w"), Id("v")), distance)));
        return All("s", N, All("n", N, All("w", words, All("v", words,
            All("h", Equal(Call("parikh", Id("v")), Call("parikh", Id("w"))), conclusion)))));
    }
}
