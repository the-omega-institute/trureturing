using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class BinaryGapProductDistributionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary gap products are counted by ordered nonunit gaps and unit-gap insertions.",
        H("Binary Gap Product Distribution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gap-product"),
                DeclarationHandle.Create("D5/S1/Digit/BinaryGapProductDistribution.gapProduct"),
                H("The product of successive binary gaps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Nat.bitIndices lists the set-bit positions in increasing order. Taking "
                    + "successive differences and multiplying them defines the gap product. "
                    + "The empty product is one, including for a number with a single set bit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gap-product-count"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.gapProductCount"),
                H("The distribution on a binary interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The count is the cardinality of the natural numbers in the half-open "
                    + "interval from two raised to n to two raised to (n + 1), "
                    + "filtered by gap product k. Thus n is precisely the top set-bit position."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positions-to-gaps"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.gaps_positions"),
                H("Successive differences undo cumulative positions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Starting at a chosen lowest position and successively adding the gaps "
                    + "recovers a list whose successive differences are exactly those gaps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaps-to-positions"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.positions_gaps"),
                H("Cumulative gaps recover sorted positions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonempty strictly increasing list, its first position and its "
                    + "successive differences reconstruct the entire list."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-gap-bijection"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.gapSequenceEquiv"),
                H("Bounded positive gaps are equivalent to binary integers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A positive gap list with sum at most n determines its lowest set bit as "
                    + "n minus that sum. The forward map sums powers of two at the cumulative "
                    + "positions; the inverse takes gaps of Nat.bitIndices. Mathlib's "
                    + "bitIndices_sum_map_two_pow verifies the binary reconstruction, and "
                    + "finite geometric-sum bounds verify the interval endpoints."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("count-through-gap-sequences"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_eq_gapSequences"),
                H("Transport the product filter through the binary bijection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original interval count equals the number of positive gap lists "
                    + "with sum at most n and product k. The proof uses explicit forward "
                    + "and inverse maps in Finset.card_bij."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reduced-tuples"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.mem_reducedTuples"),
                H("The finite index set contains exactly the required ordered tuples"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Membership in reducedTuples is equivalent to every entry being at "
                    + "least two, the ordered list's product being k, and its sum being "
                    + "at most n. Lists retain order and repeated entries; there is no "
                    + "quotient by permutation. The empty list is included when k is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("split-then-insert"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.insertUnits_splitUnits"),
                H("Unit-run compression loses no information"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "splitUnits removes each unit gap and records the lengths of the unit "
                    + "runs before, between, and after the remaining entries. Reinsertion "
                    + "recovers the original gap list exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("insert-then-split"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.splitUnits_insertUnits"),
                H("The reduced tuple and run counts are unique"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If none of the reduced entries equals one and the run-count list has "
                    + "one more entry than the reduced tuple, splitting after insertion "
                    + "returns both input lists. Together the two inverse lemmas give "
                    + "the explicit unit-gap insertion bijection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-stars-and-bars"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.card_unitPlacements"),
                H("Bounded unit-run counts satisfy stars and bars"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The number of nonnegative lists of a prescribed length with sum at "
                    + "most a given budget is the binomial coefficient choosing the length "
                    + "from budget plus length. Disjoint first-entry fibers reduce the "
                    + "proof to Mathlib's Nat.sum_range_add_choose."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reduced-fiber-cardinality"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.card_reduced_fiber"),
                H("Each reduced tuple contributes its binomial weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a reduced tuple of length r and sum s, its fiber consists of r "
                    + "plus one unit-run counts with total at most n minus s. The unused "
                    + "budget is exactly the lowest set-bit position. Its cardinality is "
                    + "the binomial coefficient choosing r plus one from n minus s plus "
                    + "r plus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gap-product-composition-sum"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution."
                    + "gapProductCount_eq_composition_sum"),
                H("The binary gap-product distribution is the ordered-tuple sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Sum the preceding fiber cardinalities over all ordered tuples whose "
                    + "entries are at least two, product is k, and sum is at most n. "
                    + "Finset.card_eq_sum_card_fiberwise partitions the bounded positive "
                    + "gap lists by their reduced tuple. The theorem holds for all natural "
                    + "n and k, and hence in particular for every positive k as requested "
                    + "in the general binary-gap question MO 469990."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-one-empty-tuple"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_one"),
                H("The empty tuple contributes n plus one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A reduced tuple with product one must be empty. Specializing the "
                    + "composition sum gives exactly n plus one numbers with gap product "
                    + "one. A separate kernel-decided sanity example checks that the "
                    + "count for n equal to four and k equal to two is six."))),
                DescribeRole.Theorem))));
}
