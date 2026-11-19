using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift;

internal sealed class PreparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private arithmetic and schedule lemmas for the ordered-cone joint lift",
        H("Ordered-cone joint lift preparation"),
        Blocks(
            Paragraph(Text("The endpoint proof uses these private helpers to verify the floor mask, the signed heights at the three negative labels, and the zero total for the doubled source.")),
            Describe.Lean(DescribeId.Create("ordered-cone-schedule"),
                DeclarationHandle.Create(Prefix + "ordered_schedule"),
                H("Prefix bounds from the physical schedule"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a word with three negative steps, the helper applies the equal-outer source bridge to the given permutation, nonnegative blocks, seam bounds, and zero total. Every prefix then lies in the strip of heights from zero to the specified capacity."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("ordered-cone-floor-mask"),
                DeclarationHandle.Create(Prefix + "core_from_floor"),
                H("Lower bound from the floor remainder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If L minus u is B times v plus a remainder smaller than B, then B times v is at least L minus u minus B. The given lower bound on that difference yields the required nonnegative margin after adding r times (s plus one) and subtracting p times (t plus one)."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("ordered-cone-doubled-source"),
                DeclarationHandle.Create(Prefix + "doubled_source_zero_cast"),
                H("Zero total for the doubled source"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a length of at least three and an integer seed given as a cast of a natural seed, the equal-outer source bridge gives zero total for the centered increments over the complete cycle at twice that seed."))),
                DescribeRole.Lemma)), []));
}
