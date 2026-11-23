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
                "Prescribe occupancies between zero and one with adjacent sums at most one. Complement "
                + "the odd-indexed events and their marginals. For any target at or after a fixed source, "
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
                "For any finite profile satisfying the same bounds, the indicator of each occupied "
                + "event yields a word with no adjacent ones. The site measures are the prescribed "
                + "occupancies. The oriented differences after alternating complementation reach their "
                + "bounds simultaneously from the chosen source to all later targets.",
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Entry(string id, string declaration, string title,
        string statement, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
