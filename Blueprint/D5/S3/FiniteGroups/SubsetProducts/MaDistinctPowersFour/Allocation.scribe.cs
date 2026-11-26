using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaAllocationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Allocate disjoint exponent positions to classes of sizes one through four.",
        H("Allocate disjoint exponent positions to classes of sizes one through four"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-allocation-card-classpositions"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.card_classPositions"),
                H("card_classPositions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Sum the number of positions over each populated class-size bucket."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-allocation-slot-lt"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.slot_lt"),
                H("slot_lt"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Each allotted position is below n when the class counts account for n elements."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-allocation-slot-injective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.slot_injective"),
                H("slot_injective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("The two endpoint ranges and the disjoint middle intervals make the assignment injective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-allocation-pair-slots"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.pair_slots"),
                H("pair_slots"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Each pair receives distinct complementary exponents whose sum is n + 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-allocation-triple-slots"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.triple_slots"),
                H("triple_slots"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Each triple gets three consecutive exponents after the first endpoint range."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-allocation-four-slots"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.four_slots"),
                H("four_slots"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Each quadruple gets four consecutive exponents after the triples."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-allocation-classpositions"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.ClassPositions"),
                H("ClassPositions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text(
                    "The abbreviation `ClassPositions (count : Fin 4 → ℕ) : Type` is "
                    + "`Σ k : Fin 4, Fin (count k) × Fin (k.val + 1)`. The index `k` records the class size minus one. "
                    + "The two finite indices select a class of that size and a position within it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-allocation-slot"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.slot"),
                H("slot"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(
                    Paragraph(Text(
                        "`slot (n : ℕ) (count : Fin 4 → ℕ) (k : Fin 4) (i : Fin (count k)) "
                        + "(j : Fin (k.val + 1)) : ℕ` gives the zero-based exponent position for class `i` "
                        + "of size `k.val + 1` and position `j` within the class. It matches on `k.val`.")),
                    Paragraph(Text(
                        "For `0` it gives `count 1 + 3 * count 2 + 4 * count 3 + i.val`. "
                        + "For `1` it gives `if j.val = 0 then i.val else n - (i.val + 1)`, using natural subtraction. "
                        + "For `2` it gives `count 1 + 3 * i.val + j.val`. "
                        + "The remaining case `3` gives `count 1 + 3 * count 2 + 4 * i.val + j.val`."))),
                DescribeRole.Definition))));
}
