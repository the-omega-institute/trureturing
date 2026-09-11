using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class FirstSumsPartitionCharacterizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/wiseman2025a391620");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A decreasing partition is not a first-sums list exactly when it has a part below four.",
        H("First Sums of Decreasing Partitions"),
        Blocks(
            Paragraph(Text("The source is Gus Wiseman's conjecture in OEIS A391620, dated "
                + "December 30, 2025. Partition parts are listed in weakly decreasing order, "
                + "and equality with the first-sums list preserves that order. For nonempty "
                + "lists, having a part below four is equivalent to having least part below four.")),
            Paragraph(Text("List(N) denotes lists of natural numbers. Pairwise applies its "
                + "relation to every earlier and later entry. All subtraction is natural "
                + "subtraction. The list characterization does not require positivity; "
                + "Mathlib Partition(n) supplies positive parts summing to n.")),
            Node("firstSums", "Adjacent sums", FirstSumsFormula(),
                "zipWith adds corresponding entries of a list and its tail. Empty lists "
                + "and singleton lists both have empty first-sums lists.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("IsFirstSums", "Realizability with parts at least two", IsFirstSumsFormula(),
                "The witness is a list of natural numbers, every entry at least two, "
                + "whose adjacent sums equal q. The empty target is allowed.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("firstSums_length", "Length of the adjacent-sums list", LengthFormula(),
                "Mathlib's zipWith length identity reduces the length to the minimum "
                + "of the lengths of x and its tail, hence length(x)-1.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("min_ge_four_of_isFirstSums", "The necessary lower bound", LowerBoundFormula(),
                "Select a realizing list. Every adjacent sum is at least 2+2, "
                + "so every entry of its first-sums list is at least four.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("isFirstSums_of_sorted_min_ge_four", "Backward reconstruction", ReconstructionFormula(),
                "For a singleton [a], use [a-2,2]. Given a realization of the suffix "
                + "beginning at b whose first entry u satisfies 2 <= u <= b-2, "
                + "prepend a-u. Since b <= a, this new entry is at least two "
                + "and at most a-2, and its sum with u is a. Induction constructs "
                + "a realization for every nonempty decreasing list with parts at least four.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("wiseman_conjecture", "Wiseman's characterization", ConjectureFormula(),
                "If there is no part below four, backward reconstruction supplies a "
                + "realization. Conversely, a part below four contradicts the necessary "
                + "lower bound. This proves the conjecture for the ordered-part reading.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a391620-first-sums-partition-characterization"),
                    ResolutionKind.Proved)),
            Node("card_not_firstSums_eq", "Equality of partition counts", CountFormula(),
                "Sort each partition's multiset of parts in decreasing order. Sorting "
                + "preserves membership, so the characterization makes the two filters "
                + "equal and hence their cardinalities equal. The empty list is realized "
                + "by [2], so the equality also holds at n=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a391620-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Separated(params Formula[] values)
    {
        var items = new List<Formula>();
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(values[index]);
        }
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] values) =>
        Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Separated(values)));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Lists() => Call("List", Naturals());
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);
    private static Formula Q() => F.Id("q");
    private static Formula X() => F.Id("x");
    private static Formula Y() => F.Id("y");
    private static Formula P() => F.Id("p");
    private static Formula N() => F.Id("n");
    private static Formula First(Formula x) => Call("firstSums", x);
    private static Formula Realizable(Formula q) => Call("IsFirstSums", q);
    private static Formula Universal(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula BinaryLambda(Formula operation) => Parenthesized(Seq(
        Parenthesized(Seq(F.Id("a"), Comma, Sp, F.Id("b"), Colon, Sp, Naturals())),
        Sp, Mapsto, Sp, F.Id("a"), Sp, operation, Sp, F.Id("b")));
    private static Formula Sorted(Formula q) => Call("Pairwise", BinaryLambda(Ge), q);
    private static Formula AllAtLeast(Formula list, Formula bound) => Parenthesized(
        Universal(Y(), Naturals(), Seq(Y(), Sp, InMacro, Sp, list, Sp, Implies, Sp,
            bound, Sp, Le, Sp, Y())));
    private static Formula SmallPart(Formula parts) => Parenthesized(Seq(
        Exists, Sp, Y(), Colon, Sp, Naturals(), Comma, Sp,
        Y(), Sp, InMacro, Sp, parts, Sp, Land, Sp, Y(), Sp, Lt, Sp, D(4)));
    private static Formula NonemptySorted(Formula conclusion) => Disp(Universal(Q(), Lists(), Seq(
        Q(), Sp, Neq, Sp, Nil(), Sp, Implies, Sp, Sorted(Q()), Sp, Implies, Sp, conclusion)));

    private static Formula FirstSumsFormula() => Disp(Universal(X(), Lists(), Seq(
        First(X()), Sp, Eq, Sp, Call("zipWith", BinaryLambda(Plus), X(), Call("tail", X())))));

    private static Formula IsFirstSumsFormula() => Disp(Universal(Q(), Lists(), Seq(
        Realizable(Q()), Sp, Iff, Sp, Parenthesized(Seq(
            Exists, Sp, X(), Colon, Sp, Lists(), Comma, Sp,
            AllAtLeast(X(), D(2)), Sp, Land, Sp, First(X()), Sp, Eq, Sp, Q())))));

    private static Formula LengthFormula() => Disp(Universal(X(), Lists(), Seq(
        Call("length", First(X())), Sp, Eq, Sp, Call("length", X()), Sp, Minus, Sp, D(1))));

    private static Formula LowerBoundFormula() => Disp(Universal(Q(), Lists(), Seq(
        Realizable(Q()), Sp, Implies, Sp, AllAtLeast(Q(), D(4)))));

    private static Formula ReconstructionFormula() => NonemptySorted(Seq(
        AllAtLeast(Q(), D(4)), Sp, Implies, Sp, Realizable(Q())));

    private static Formula ConjectureFormula() => NonemptySorted(Parenthesized(Seq(
        Neg, Sp, Realizable(Q()), Sp, Iff, Sp, SmallPart(Q()))));

    private static Formula Parts() => Call("parts", P());
    private static Formula PartitionType() => Call("Partition", N());
    private static Formula PartitionPredicate(Formula body) => Parenthesized(Seq(
        Parenthesized(Seq(P(), Colon, Sp, PartitionType())), Sp, Mapsto, Sp, body));
    private static Formula FilteredCount(Formula predicate) => Call("card", Call("filter",
        predicate, Parenthesized(Seq(Call("univ"), Colon, Sp, Call("Finset", PartitionType())))));
    private static Formula CountFormula() => Disp(Universal(N(), Naturals(), Seq(
        FilteredCount(PartitionPredicate(Seq(Neg, Sp,
            Realizable(Call("sort", Parts(), BinaryLambda(Ge)))))), Sp, Eq, Sp,
        FilteredCount(PartitionPredicate(SmallPart(Parts()))))));
}
