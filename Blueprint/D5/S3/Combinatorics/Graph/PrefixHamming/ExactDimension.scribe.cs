using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixHamming;

internal sealed class ExactDimensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.";
    private static readonly LibraryNoteRef Rossi =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/rossi2026permutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every ground-set size at least three, the least dimension of a unit binary Hamming cube "
        + "realizing twice Rossi's atom metric is twelve at size four and two to the ground-set size "
        + "minus two otherwise.",
        H("Exact binary Hamming dimension of permutation prefixes"),
        Blocks(
            Definition("prefix-set", "prefixSet", "Unordered prefixes",
                All("n", Naturals, All("p", Permutations, All("k", Naturals,
                    Equal(Call("prefixSet", P, K), Collection(Apply(P, F.Id("i")),
                        Member(F.Id("i"), Call("Fin", N)), Less(F.Id("i"), K)))))),
                "The prefix set collects the values at zero-based positions below k. "
                + "The rank argument is any natural number."),
            Definition("proper-ranks", "Rank", "Proper ranks",
                All("n", Naturals, Equal(Ranks, Collection(K, Member(K, Call("Fin", N)),
                    Less(D(0), K)))),
                "The proper ranks are the positive positions strictly below the ground-set size."),
            Definition("prefix-distance", "prefixDistance", "Scaled prefix distance",
                ForPermutations(Equal(Call("prefixDistance", P, Q), ScaledCount())),
                "Each proper rank at which the unordered prefixes differ contributes two."),
            Definition("cut-family", "cutFamily", "The cut family",
                All("n", Naturals, All("p", Permutations, Equal(Call("cutFamily", P),
                    Collection(Call("prefixSet", P, K), Member(K, Ranks))))),
                "The cut family contains one unordered prefix at each proper rank. Its prefix sets "
                + "have distinct cardinalities, so sorting them by size recovers the prefix chain."),
            Definition("minimum-dimension", "minimumDimension", "The dimension threshold",
                All("n", Naturals, Equal(Call("minimumDimension", N), Threshold())),
                "The threshold gives the least feasible dimension for ground-set sizes at least three."),
            Describe.Lean(
                DescribeId.Create("cut-distance-identity"),
                DeclarationHandle.Create(Prefix + "prefix_distance_eq_cut_symmDiff"),
                H("Symmetric difference of cut families"),
                StatementSource.FromAuthor(Disp(ForPermutations(Equal(Call("prefixDistance", P, Q),
                    Call("card", Seq(Call("cutFamily", P), Sp, Delta, Sp, Call("cutFamily", Q))))))),
                AssessedProvenance.FromLiterature(Rossi),
                Blocks(
                    Paragraph(Text("At every ground-set size and for any two permutations, the scaled "
                        + "prefix distance equals the cardinality of the symmetric difference of their "
                        + "cut families.")),
                    Paragraph(Text("Represent each nonempty proper subset by its rank and the subset "
                        + "itself. The subset cardinality determines the rank. Within a rank, the two "
                        + "incidence words differ at exactly two coordinates when their prefixes differ, "
                        + "and at zero when they agree. Forgetting the rank gives a bijection from "
                        + "differing incidence coordinates to the symmetric difference."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-binary-hamming-dimension"),
                DeclarationHandle.Create(Prefix + "minimum_hamming_dimension"),
                H("Exact dimension and all feasible paddings"),
                StatementSource.FromAuthor(Disp(DimensionStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each natural n at least three and each natural d, the formula "
                        + "asks for one map on all permutations into d Boolean coordinates. The "
                        + "ordinary Hamming distance of its two values must exactly equal twice the "
                        + "number of unequal proper prefixes for every pair. The cut families recover "
                        + "the permutations, so preservation at this scale implies injectivity.")),
                    Paragraph(Text("For the lower bound, an adjacent exchange at a rank gives the "
                        + "difference of two prefix-incidence basis vectors. Paths of exchanges realize "
                        + "every difference at that rank. Polarization transfers the pairings of these "
                        + "integer sums to any distance-preserving binary map. At a fixed rank, subtract "
                        + "one reference basis vector. The resulting nonzero vectors have two signed "
                        + "coordinates each and pairwise inner product one. Their supports are distinct "
                        + "intersecting pairs, hence form a star or a triangle. Orthogonality across "
                        + "ranks forces disjoint coordinate supports. Adding the resulting rank bounds "
                        + "gives the stated threshold.")),
                    Paragraph(Text("For attainment, concatenate one-hot words for the possible "
                        + "prefixes at each rank. A rank with four prefixes uses instead the "
                        + "three-bit words 000, 011, 101, and 110, which have distance two for "
                        + "distinct words. For n at least three this saving occurs only at the two "
                        + "outer ranks for n equal to four. Extra zero coordinates preserve every "
                        + "distance, giving the map for all dimensions above the threshold."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula DimensionStatement()
    {
        var f = F.Id("f");
        var d = F.Id("d");
        var word = Seq(Call("Fin", d), Sp, To, Sp, Named("Bool"));
        var maps = Seq(Permutations, Sp, To, Sp, word);
        var distance = Call("hammingDist", Apply(f, P), Apply(f, Q));
        var preserves = All("p", Permutations, All("q", Permutations,
            Equal(distance, ScaledCount())));
        var exists = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("f"),
            maps, preserves);
        return All("n", Naturals, All("d", Naturals, new Formula.Logic(
            Relation(D(3), FormulaRelationOperator.LessThanOrEqual, N),
            FormulaLogicOperator.Implies,
            Parentheses(new Formula.Logic(Parentheses(exists), FormulaLogicOperator.Iff,
                Relation(Threshold(), FormulaRelationOperator.LessThanOrEqual, d))))));
    }

    private static Formula N => F.Id("n");
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
    private static Formula K => F.Id("k");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Permutations => Call("Perm", Call("Fin", N));
    private static Formula Ranks => Call("Rank", N);
    private static Formula ForPermutations(Formula body) =>
        All("n", Naturals, All("p", Permutations, All("q", Permutations, body)));

    private static Formula ScaledCount() => new Formula.Binary(D(2), FormulaBinaryOperator.Multiply,
        Call("card", Collection(K, Member(K, Ranks),
            Relation(Call("prefixSet", P, K), FormulaRelationOperator.NotEqual, Call("prefixSet", Q, K)))));

    private static Formula Threshold() => Seq(Begin, Grp(F.Id("cases")),
        D(1, 2), Amp, Equal(N, D(4)), RowBreak,
        new Formula.Binary(new Formula.Power(D(2), N), FormulaBinaryOperator.Subtract, D(2)),
        Amp, Seq(F.Text, Grp(F.Id("otherwise"))), End, Grp(F.Id("cases")));

    private static Formula Collection(Formula element, Formula binder, Formula? restriction = null) =>
        Seq(OpenBrace, element, Sp, Mid, Sp, binder,
            restriction is null ? CloseBrace : Seq(Comma, Sp, restriction, CloseBrace));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Parentheses(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] values) => Apply(Named(name), values);
    private static Formula Apply(Formula function, params Formula[] values) =>
        new Formula.Apply(function, [.. values]);
    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Less(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThan, right);
}
