using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class FIBPathPairBoundsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Words/AdmissibleWords/FIBPathPairBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cumulative downward variation bounds the oriented difference between two sites.",
        H("Sharp path occupancy bounds from a fixed start"),
        Blocks(
            Entry("variation", "downwardVariation", "Downward variation between two sites",
                "Starting at the chosen site, add the positive part of each successive decrease in the "
                + "transformed profile up to the target site.", DescribeRole.Definition),
            Entry("hard-core-bound", "sharp_hard_core_difference", "The sharp event difference",
                "Prescribe nonnegative occupancies with adjacent sums at most one, which also bounds "
                + "each occupancy by one. Consider "
                + "measurable events in the half-open unit interval with the prescribed occupancies "
                + "and pointwise disjoint adjacent events. Complement the odd-indexed events within "
                + "that interval and complement their marginals. For any target at or after a fixed source, "
                + "the mass in the transformed source event outside the transformed target event is at "
                + "most the least of the source mass, the complement of the target mass, and the downward "
                + "variation between them. One family of measurable occupation events attains the bound "
                + "for every such target. Divide the unit interval at the transformed source mass. In each "
                + "part use an initial interval. Choose the first length as the maximum of zero, the "
                + "source plus target mass minus one, and the source mass minus the downward variation. "
                + "Before the source use the lesser of the two masses. The second length supplies the "
                + "rest of the prescribed mass. Both lengths follow the direction of each adjacent "
                + "change, giving nested transformed events and disjoint adjacent occupied events.",
                DescribeRole.Theorem),
            Entry("finite-word", "word_attainment", "One law on admissible finite words",
                "For a finite profile whose occupancies lie between zero and one and whose adjacent "
                + "sums are at most one, the indicator of each occupied "
                + "event yields a word with no adjacent ones. The site measures are the prescribed "
                + "occupancies, and each occupancy event is measurable and contained in the "
                + "half-open unit interval. The oriented differences within the interval after "
                + "alternating complementation reach their "
                + "bounds simultaneously from the chosen source to all later targets.",
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Entry(string id, string declaration, string title,
        string statement, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
