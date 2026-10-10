using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class LeSaulnierVijayLowerDensityRefutationDensityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eleven-adic interval construction has lower density at least four fifteenths.",
        H("Counting the Eleven-Adic Interval Construction"),
        Blocks(
            Node("lv-density-scale", "Stage scale", "M",
                "For every natural stage index k, the scale M is the natural quotient of "
                    + "eleven to the power k plus one by two.", DescribeRole.Definition),
            Node("lv-density-stage", "The two stage intervals", "stage",
                "Stage k is the union of the inclusive intervals from twice M to three M "
                    + "minus one, and from six M minus two to eleven M minus five.",
                DescribeRole.Definition),
            Node("lv-density-set", "The infinite witness set", "S",
                "The witness consists of one and all integers in any of the stage intervals.",
                DescribeRole.Definition),
            Node("lv-density-even-scale", "The exact doubled scale", "twice_M",
                "For every natural k, twice the scale is exactly eleven to the power k "
                    + "plus one; eleven to every natural power is odd.", DescribeRole.Theorem),
            Node("lv-density-positive-scale", "Every scale is positive", "M_pos",
                "The scale is strictly positive for every natural stage index.",
                DescribeRole.Theorem),
            Node("lv-density-scale-recurrence", "The scale recurrence", "M_step",
                "The next scale is eleven times the present scale minus five.",
                DescribeRole.Theorem),
            Node("lv-density-increasing-scale", "The scales strictly increase", "M_strictMono",
                "The scale function is strictly increasing on the natural numbers.",
                DescribeRole.Theorem),
            Node("lv-density-stage-bounds", "Stage bounds", "stage_bounds",
                "Every member of stage k is at least twice its scale and at most the scale "
                    + "of stage k plus one.", DescribeRole.Theorem),
            Node("lv-density-positive-set", "The witness uses positive integers", "S_pos",
                "Every integer in the witness set is strictly positive.", DescribeRole.Theorem),
            Node("lv-density-liminf-bound", "Lower density at least four fifteenths",
                "lowerDensityBound",
                "The atTop liminf of the real sequence formed by the number of witness "
                    + "integers in the inclusive interval from one to n, divided by n, is "
                    + "at least four fifteenths. This is the lower-density definition used "
                    + "in the conjecture. For every n at least one, fifteen times the count "
                    + "is at least four n. A finite prefix through each stage scale has "
                    + "count C satisfying five C at least three M plus two. Truncating the "
                    + "next two intervals at n gives the bound throughout each interval "
                    + "and gap. The sequence is at most one, and the counting inequality "
                    + "supplies its eventual lower bound.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
