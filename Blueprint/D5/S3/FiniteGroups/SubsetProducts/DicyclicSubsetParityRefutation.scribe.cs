using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts;

internal sealed class DicyclicSubsetParityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/mandalneetu2026dicyclic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three subset classes in Mandal--Neetu Question 6.3 cannot all have even counts: Dic12 has 495 four-element subsets.",
        H("An odd total refutes universal dicyclic subset parity"),
        Blocks(
            Paragraph(Text(
                "The five finite-set definitions fix the operations and counts used by the exact "
                + "affirmative claim and its literal negation.")),
            Describe.Lean(
                DescribeId.Create("dicyclic-subset-product-set"),
                DeclarationHandle.Create(Prefix + "productSet"),
                H("The duplicate-free product set"),
                StatementSource.FromAuthor(Disp(SetDefinition("productSet", inverse: false))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For an implicit G : Type* in any universe, with instances [Group G] and "
                    + "[DecidableEq G], and A : Finset G, productSet A : Finset G is "
                    + "(A.product A).image (fun xy => xy.1 * xy.2). The image ranges over every "
                    + "ordered pair in A times A and removes repeated values; it neither requires "
                    + "distinct factors nor assumes commutativity or finiteness of G. This is the "
                    + "paper's product interpretation of A+A, Main.tex line 120."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dicyclic-subset-right-quotient-set"),
                DeclarationHandle.Create(Prefix + "rightQuotientSet"),
                H("The duplicate-free right quotient set"),
                StatementSource.FromAuthor(Disp(SetDefinition("rightQuotientSet", inverse: true))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For an implicit G : Type* in any universe, with instances [Group G] and "
                    + "[DecidableEq G], and A : Finset G, rightQuotientSet A : Finset G is "
                    + "(A.product A).image (fun xy => xy.1 * xy.2⁻¹). Every ordered pair is "
                    + "included and repeated values are removed. The inverse is on the second "
                    + "factor, on the right of the first; no commutativity or finiteness of G "
                    + "is assumed. This is A-A as defined in Main.tex line 120."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dicyclic-subset-sum-dominant-count"),
                DeclarationHandle.Create(Prefix + "sumDominantCount"),
                H("All sum-dominant subsets of a given size"),
                StatementSource.FromAuthor(Disp(CountDefinition("sumDominantCount",
                    FormulaRelationOperator.GreaterThan))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For explicit G : Type* in any universe, instances [Group G], [Fintype G] "
                    + "and [DecidableEq G], and m : ℕ, sumDominantCount G m : ℕ is "
                    + "((univ : Finset G).powersetCard m |>.filter (fun A => "
                    + "(rightQuotientSet A).card < (productSet A).card)).card. The displayed "
                    + "greater-than comparison is the same strict inequality with its sides "
                    + "reversed. The local Classical.propDecidable instance decides the filter. "
                    + "Every distinct m-element subset of G is considered once, without a type "
                    + "restriction or symmetry quotient. The definition applies to every natural "
                    + "m, with no bounds imposed here. It represents S in Main.tex lines 183–187."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dicyclic-subset-difference-dominant-count"),
                DeclarationHandle.Create(Prefix + "differenceDominantCount"),
                H("All difference-dominant subsets of a given size"),
                StatementSource.FromAuthor(Disp(CountDefinition("differenceDominantCount",
                    FormulaRelationOperator.LessThan))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For explicit G : Type* in any universe, instances [Group G], [Fintype G] "
                    + "and [DecidableEq G], and m : ℕ, differenceDominantCount G m : ℕ is "
                    + "((univ : Finset G).powersetCard m |>.filter (fun A => "
                    + "(productSet A).card < (rightQuotientSet A).card)).card. The comparison "
                    + "is strict. The local Classical.propDecidable instance decides the filter. "
                    + "Every distinct m-element subset is considered once, without a type "
                    + "restriction or symmetry quotient, for every natural m without further "
                    + "bounds. This is D in Main.tex lines 183–187."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dicyclic-subset-balanced-count"),
                DeclarationHandle.Create(Prefix + "balancedCount"),
                H("All balanced subsets of a given size"),
                StatementSource.FromAuthor(Disp(CountDefinition("balancedCount",
                    FormulaRelationOperator.Equal))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For explicit G : Type* in any universe, instances [Group G], [Fintype G] "
                    + "and [DecidableEq G], and m : ℕ, balancedCount G m : ℕ is "
                    + "((univ : Finset G).powersetCard m |>.filter (fun A => "
                    + "(productSet A).card = (rightQuotientSet A).card)).card. The local "
                    + "Classical.propDecidable instance decides this equality filter. Every "
                    + "distinct m-element subset is considered once, without a type restriction "
                    + "or symmetry quotient, for every natural m without further bounds. This "
                    + "is B in Main.tex lines 183–187."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dicyclic-subset-parity-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The full affirmative answer to Question 6.3"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Mandal and Neetu, arXiv:2602.09073v1, Question 6.3, ask whether all three "
                        + "counts S, D and B are even for every positive integer n at least three and "
                        + "every integer m between two and 2n inclusive. The claim includes both odd "
                        + "and even n. Its natural-number bounds imply positivity; the local NeZero n "
                        + "instance only supplies the finite-group structure.")),
                    Paragraph(Text(
                        "QuaternionGroup n is Mathlib's dicyclic group of order 4n, with generators "
                        + "a and x corresponding to the paper's a and b. The paper writes A+A for "
                        + "the product set of all xy with x,y in A, and A-A for the right quotient "
                        + "set of all x times the inverse of y. Finset images remove duplicates. "
                        + "The universe is univ.powersetCard m: every distinct m-element subset of "
                        + "the actual group appears once, without a type restriction or quotient by symmetry.")),
                    Paragraph(Text(
                        "sumDominantCount counts subsets with product cardinality strictly larger "
                        + "than right quotient cardinality; differenceDominantCount uses strictly "
                        + "smaller, and balancedCount uses equality. The assertion is the conjunction "
                        + "of Even on these three natural counts. It uses the paper's unrestricted "
                        + "S, D and B, rather than its separately defined counts restricted to a given type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dicyclic-subset-parity-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The instance n = 3 and m = 4 contradicts the conjunction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The result has type Not claim. For any finite collection and two "
                        + "natural-valued functions, the comparisons greater, smaller and equal "
                        + "partition that collection. The private comparison_partition identity "
                        + "expresses this by two filter-cardinality splits. Applied to product "
                        + "and right quotient cardinalities on all m-subsets, counts_total gives "
                        + "S + D + B = choose(card G,m), using Finset.card_powersetCard.")),
                    Paragraph(Text(
                        "Take n = 3 and m = 4, which satisfy every stated bound. "
                        + "QuaternionGroup.card gives card G = 12, so the total is "
                        + "choose(12,4) = 495. If all three counts were even, their sum would be "
                        + "even. The odd total contradicts that consequence and refutes the "
                        + "universal affirmative answer.")),
                    Paragraph(Text(
                        "This argument does not identify an individual odd class, enumerate a "
                        + "group table, or assert that any particular count is always odd. "
                        + "It leaves the paper's preceding m = 2,3 observations and its other "
                        + "questions separate. An even total alone would not imply that all "
                        + "three counts are even. The source note fixes the cited version and "
                        + "interpretation; no first-resolution or worldwide priority claim is made."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mandal-neetu-dicyclic-question-63-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Qualified(string owner, string name) => Seq(F.Id(owner), Dot, F.Id(name));
    private static Formula FinsetCall(string name, params Formula[] arguments) =>
        new Formula.Apply(Qualified("Finset", name), [.. arguments]);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula GroupScope(Formula body, bool finite)
    {
        var g = F.Id("G");
        return Seq(Forall, Sp, Typed(g, Seq(F.Id("Type"), Star)), Sp,
            Instance("Group", g),
            finite ? Instance("Fintype", g) : Seq(),
            Instance("DecidableEq", g), Comma, Sp, Parenthesized(body));
    }

    private static Formula SetDefinition(string name, bool inverse)
    {
        var g = F.Id("G");
        var a = F.Id("A");
        var xy = F.Id("xy");
        Formula second = Seq(xy, Dot, D(2));
        if (inverse)
            second = new Formula.Power(Parenthesized(second), Seq(Minus, D(1)));
        var value = new Formula.Binary(Seq(xy, Dot, D(1)), FormulaBinaryOperator.Multiply, second);
        var map = Parenthesized(Seq(Typed(xy, Seq(g, Sp, Times, Sp, g)), Sp, Mapsto, Sp, value));
        var rhs = FinsetCall("image", map, FinsetCall("product", a, a));
        return GroupScope(All("A", Call("Finset", g), new Formula.Relation(
            Typed(Call(name, a), Call("Finset", g)), FormulaRelationOperator.Equal, rhs)), finite: false);
    }

    private static Formula CountDefinition(string name, FormulaRelationOperator comparison)
    {
        var g = F.Id("G");
        var m = F.Id("m");
        var a = F.Id("A");
        var condition = new Formula.Relation(FinsetCall("card", Call("productSet", a)),
            comparison, FinsetCall("card", Call("rightQuotientSet", a)));
        var predicate = Parenthesized(Seq(Typed(a, Call("Finset", g)), Sp, Mapsto, Sp, condition));
        var subsets = FinsetCall("powersetCard", m, Typed(Qualified("Finset", "univ"), Call("Finset", g)));
        var rhs = FinsetCall("card", FinsetCall("filter", predicate, subsets));
        return GroupScope(All("m", Nat(), new Formula.Relation(
            Typed(Call(name, g, m), Nat()), FormulaRelationOperator.Equal, rhs)), finite: true);
    }
}
