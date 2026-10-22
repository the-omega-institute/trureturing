using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class PackingMaximumRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/blitvickammounsteingrimsson2026patterns");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The interleaved minimal pattern need not maximize the prescribed packing count.",
        H("A counterexample to packing-maximum Conjecture 7.1"),
        Blocks(
            Paragraph(Text("Blitvic, Kammoun and Steingrimsson, arXiv:2610.29846v1, Conjecture 7.1: "
                + "“For overlap m ≤ K/2, the maximum is obtained when prefix and suffix are interleaved and minimal, "
                + "that is, for patterns with prefix 135…(2m−1) and suffix 246…(2m).” "
                + "A maximum-attainment assertion means that a prescribed pattern exists whose count dominates "
                + "every compatible comparison pattern. Its middle order is unrestricted. No uniqueness of a maximum is asserted.")),
            Definition("entry", "Zero-based one-line entries", "entry", Entries(),
                "Both positions and ranks use Fin(n)={0,…,n−1}. Adding one to a position and its rank gives the source's "
                + "one-based notation; strict comparisons are unchanged. entry(w,i) is the i-th entry of the finite list of ranks, "
                + "with default zero outside the list. Prefix and suffix queries are in range throughout the asserted parameter domain."),
            Definition("window-index", "Positions in prescribed windows", "windowIndex", Indices(),
                "The window indexed by t in Fin(j) begins at t(K−m), which is source position 1+t(K−m). "
                + "For a in Fin(K), t(K−m)+a is below n=K+(j−1)(K−m): t≤j−1 and multiplication by K−m preserves this bound. "
                + "The Fin-valued construction includes this bound, so no window lookup uses an out-of-range default."),
            Definition("packs", "All prescribed source occurrences", "Packs", Packing(),
                "Definition 2.2 uses agreement of every pairwise strict comparison. Definition 2.6 and equation (2.1) "
                + "require precisely j contiguous windows of length K at the prescribed starts. The displayed predicate tests "
                + "every pair in every such window. Remark 2.7 permits additional occurrences; this predicate makes no test "
                + "at any other start and places no avoidance condition on the permutation."),
            Definition("source-packing", "The actual source permutations", "SourcePacking", SourcePackings(),
                "A source packing is an equivalence Fin(n)→Fin(n) whose one-line values satisfy Packs. "
                + "Thus each rank occurs once. Its elements are actual labeled permutations, rather than equivalence classes, "
                + "posets or lists of occurrence locations."),
            Definition("count", "The original packing cardinality", "count", Counting(),
                "count(p,m,j) is the natural cardinality of SourcePacking(p,m,j), the set denoted S_p^m(j) in the source. "
                + "It counts each source permutation once, including permutations with extra occurrences."),
            Definition("admissible", "Compatible comparison patterns", "Admissible", Admissibility(),
                "The pattern is injective on Fin(K), hence bijective because its domain and codomain are the same finite set. "
                + "The m-prefix and m-suffix agree on all pairwise strict comparisons, as required after Definition 3.3. "
                + "No increasing-order or first-value hypothesis narrows this domain. The source's normalized presentation "
                + "uses increasing prefix and suffix with the first prefix value smaller; the two displayed patterns already obey it."),
            Definition("prescribed", "Every prescribed middle order remains available", "Prescribed", Prescription(),
                "For each a=0,…,m−1 the prefix rank is 2a and the suffix rank at K−m+a is 2a+1. "
                + "After adding one these are 1,3,…,2m−1 and 2,4,…,2m. Together with Admissible, "
                + "these equations leave every ordering of the remaining ranks 2m,…,K−1 in the middle."),
            Definition("whole-claim", "The full existential maximum-attainment assertion", "claim", WholeClaim(),
                "All natural K,m,j satisfying K≥2, 1≤m<K, 2m≤K and j≥1 are quantified. For each triple there must "
                + "exist an admissible prescribed rho dominating every admissible pi. The equality boundary 2m=K and j=1 "
                + "are included. There is no fixed middle order, restriction on other occurrences or quotient by symmetry."),
            Definition("competitor", "The pattern 13472568", "competitor",
                Eq(V("competitor"), Call("vector", D(0), D(2), D(3), D(6), D(1), D(4), D(5), D(7))),
                "This is the zero-based vector for 13472568. Its prefix 1347 and suffix 2568 are increasing, "
                + "with first values 1<2; in particular it is source-admissible at m=4."),
            Definition("prescribed-pattern", "The pattern 13572468", "prescribed",
                Eq(V("prescribed"), Call("vector", D(0), D(2), D(4), D(6), D(1), D(3), D(5), D(7))),
                "This is the zero-based vector for 13572468, with the prescribed prefix 1357 and suffix 2468."),
            Definition("encoding", "An exact two-way rank-assignment correspondence", "encodingEquiv",
                Parameters(F.Seq(Call("encodingEquiv", V("p"), V("m"), V("j")), F.Colon,
                    Call("Equiv", Call("SourcePacking", V("p"), V("m"), V("j")), Encoded()))),
                "Sending an actual permutation to its underlying rank function preserves every window comparison. "
                + "Conversely, an injective rank function on the same finite set is bijective by Mathlib's "
                + "Finite.injective_iff_bijective, so Equiv.ofBijective reconstructs the source permutation. "
                + "Both composites are identities. This is the direct rank-assignment counterpart of the source's "
                + "Lemma 5.1 and Theorem 5.3; it introduces neither a labeling factor nor a missing inverse-permutation convention."),
            Theorem("cardinality", "Cardinality without representation multiplicity", "source_cardinality",
                All("K", Nat, All("m", Nat, All("j", Nat, All("p", Words(V("K")),
                    Eq(Call("count", V("p"), V("m"), V("j")), Call("card", Encoded())))))),
                "Nat.card_congr transports the original count through encodingEquiv. The encoded subtype consists "
                + "of all injective rank assignments satisfying the same pairwise window predicate, in both directions."),
            Theorem("nine", "Nine packings of 13472568", "count_competitor",
                Eq(Call("count", V("competitor"), D(4), D(2)), D(9)),
                "Here n=12 and the windows begin at source positions 1 and 5. Writing x_i for the source entries, "
                + "their exact chains are x1<x5<x2<x3<x6<x7<x4<x8 and x5<x9<x6<x7<x10<x11<x8<x12. "
                + "They are equivalent to ordered groups x1 < x5 < {x2,x3,x9} < x6 < x7 < {x4,x10,x11} < x8 < x12, "
                + "with x2<x3 and x10<x11 inside the two three-element groups. The first group receives ranks 3,4,5 "
                + "in three ways, and the second receives 8,9,10 in three ways. The other ranks are forced. "
                + "The finite certificate contains the nine resulting one-line rank functions. Its membership equivalence "
                + "proves completeness from the source chains and injectivity, and checks every original comparison "
                + "for each listed function. Fintype.card_of_subtype and the exact cardinality bridge give 9."),
            Theorem("eight", "Eight packings of 13572468", "count_prescribed",
                Eq(Call("count", V("prescribed"), D(4), D(2)), D(8)),
                "The exact chains are x1<x5<x2<x6<x3<x7<x4<x8 and x5<x9<x6<x10<x7<x11<x8<x12. "
                + "Their ordered groups are x1 < x5 < {x2,x9} < x6 < {x3,x10} < x7 < {x4,x11} < x8 < x12. "
                + "The pairs receive ranks {3,4}, {6,7} and {9,10}, with either order in each pair; singleton ranks "
                + "are 1,2,5,8,11,12. The eight resulting functions are precisely the injective source packings, "
                + "as established by the two-way certificate membership proof. Cardinality transport therefore gives 8."),
            Theorem("boundary", "The full prescribed family at the equality boundary", "prescribed_boundary",
                All("p", Words(D(8)), Imp(Call("Prescribed", V("p"), D(4)), Eq(V("p"), V("prescribed")))),
                "At K=8,m=4 the middle is empty. The four prefix equations and four suffix equations determine "
                + "all eight entries, so every prescribed candidate is 13572468. This is a statement about the "
                + "entire prescribed family at this boundary, without a global uniqueness assumption."),
            Theorem("refutation", "A strict count inequality refutes the whole assertion", "result",
                new Formula.Not(V("claim")),
                "Specializing the whole claim to K=8,m=4,j=2 would produce a prescribed rho dominating every "
                + "compatible pattern. The boundary theorem forces rho=13572468, while the admissible pattern "
                + "13472568 has 9 packings and rho has 8. The impossible inequality 9≤8 refutes the full claim. "
                + "It does not identify the actual maximum, settle the strict-overlap range 2m<K, or answer "
                + "the separate cutoff question in Section 7 item 8. The difference is two independent three-way "
                + "choices versus three independent binary choices, rather than an avoidance or labeling effect.")
        ), []));

    private static DocumentBlock Definition(string id, string title, string name, Formula formula, string prose) =>
        Entry(id, title, name, formula, prose, DescribeRole.Definition);
    private static DocumentBlock Theorem(string id, string title, string name, Formula formula, string prose) =>
        Entry(id, title, name, formula, prose, DescribeRole.Theorem);
    private static DocumentBlock Entry(string id, string title, string name, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)),
            (role == DescribeRole.Theorem || name is "competitor" or "encodingEquiv") ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result"
                ? new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("blitvic-kammoun-steingrimsson-2026-packing-maximum"),
                    ResolutionKind.Refuted)
                : null);

    private static Formula V(string s) => F.Id(s);
    private static Formula Nat => F.Seq(F.Mathbb, F.Grp(V("N")));
    private static Formula Call(string s, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. args]);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Words(Formula n) => new Formula.TypeArrow(Fin(n), Fin(n));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Some(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), type, body);
    private static Formula Length => Add(V("K"), Mul(Sub(V("j"), D(1)), Sub(V("K"), V("m"))));
    private static Formula Position(Formula a) => Add(Mul(Call("val", V("t")), Sub(V("K"), V("m"))), Call("val", a));
    private static Formula EntryAt(Formula p, Formula a) => Call("entry", p, a);
    private static Formula Lambda(string name, Formula body) => F.Seq(V(name), F.Mapsto, body);
    private static Formula Parameters(Formula body) => All("K", Nat,
        All("p", Words(V("K")), All("m", Nat, All("j", Nat, body))));
    private static Formula AtWindow(string letter) => Call("w",
        Call("windowIndex", V("K"), V("m"), V("j"), V("t"), V(letter)));
    private static Formula Entries()
    {
        var lookup = Call("getD", Call("ofFn", Lambda("k", Call("val", Call("w", V("k"))))), V("i"), D(0));
        return All("n", Nat, All("w", Words(V("n")), All("i", Nat,
            Eq(Call("entry", V("w"), V("i")), lookup))));
    }
    private static Formula Indices()
    {
        var equation = Eq(Call("val", Call("windowIndex", V("K"), V("m"), V("j"), V("t"), V("a"))), Position(V("a")));
        return All("K", Nat, All("m", Nat, All("j", Nat,
            All("t", Fin(V("j")), All("a", Fin(V("K")), equation)))));
    }
    private static Formula Packing()
    {
        var comparisons = Iff(Lt(AtWindow("a"), AtWindow("b")), Lt(Call("p", V("a")), Call("p", V("b"))));
        var windows = All("t", Fin(V("j")), All("a", Fin(V("K")), All("b", Fin(V("K")), comparisons)));
        return Parameters(All("w", Words(Length), Iff(Call("Packs", V("p"), V("m"), V("j"), V("w")), windows)));
    }
    private static Formula SourcePackings()
    {
        var subtype = Call("Subtype", Call("Perm", Fin(Length)),
            Lambda("w", Call("Packs", V("p"), V("m"), V("j"), V("w"))));
        return Parameters(Eq(Call("SourcePacking", V("p"), V("m"), V("j")), subtype));
    }
    private static Formula Counting() => Parameters(Eq(Call("count", V("p"), V("m"), V("j")),
        Call("card", Call("SourcePacking", V("p"), V("m"), V("j")))));
    private static Formula Admissibility()
    {
        var prefix = Lt(EntryAt(V("p"), Call("val", V("a"))), EntryAt(V("p"), Call("val", V("b"))));
        var suffix = Lt(EntryAt(V("p"), Add(Sub(V("K"), V("m")), Call("val", V("a")))),
            EntryAt(V("p"), Add(Sub(V("K"), V("m")), Call("val", V("b")))));
        var compatibility = All("a", Fin(V("m")), All("b", Fin(V("m")), Iff(prefix, suffix)));
        return All("K", Nat, All("p", Words(V("K")), All("m", Nat,
            Iff(Call("Admissible", V("p"), V("m")), And(Call("Injective", V("p")), compatibility)))));
    }
    private static Formula Prescription()
    {
        var prefix = All("a", Fin(V("m")), Eq(EntryAt(V("p"), Call("val", V("a"))), Mul(D(2), Call("val", V("a")))));
        var suffix = All("a", Fin(V("m")), Eq(EntryAt(V("p"), Add(Sub(V("K"), V("m")), Call("val", V("a")))),
            Add(Mul(D(2), Call("val", V("a"))), D(1))));
        return All("K", Nat, All("p", Words(V("K")), All("m", Nat,
            Iff(Call("Prescribed", V("p"), V("m")), And(prefix, suffix)))));
    }
    private static Formula Encoded() => Call("Subtype", Words(Length), Lambda("w",
        And(Call("Injective", V("w")), Call("Packs", V("p"), V("m"), V("j"), V("w")))));
    private static Formula WholeClaim()
    {
        var domination = All("pi", Words(V("K")), Imp(Call("Admissible", V("pi"), V("m")),
            Le(Call("count", V("pi"), V("m"), V("j")), Call("count", V("rho"), V("m"), V("j")))));
        var maximal = Some("rho", Words(V("K")), And(Call("Admissible", V("rho"), V("m")),
            And(Call("Prescribed", V("rho"), V("m")), domination)));
        var body = Imp(Le(D(2), V("K")), Imp(Le(D(1), V("m")), Imp(Lt(V("m"), V("K")),
            Imp(Le(Mul(D(2), V("m")), V("K")), Imp(Le(D(1), V("j")), maximal)))));
        return Iff(V("claim"), All("K", Nat, All("m", Nat, All("j", Nat, body))));
    }
}
