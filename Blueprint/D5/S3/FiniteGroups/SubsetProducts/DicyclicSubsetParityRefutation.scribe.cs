using static StrataLint.Scribe.DefinitionDsl;

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
                "The linked Lean declarations give the exact affirmative claim and its literal negation. "
                + "No statement formula is supplied here; the following paragraphs are authored exposition.")),
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
                DescribeRole.Theorem))));
}
