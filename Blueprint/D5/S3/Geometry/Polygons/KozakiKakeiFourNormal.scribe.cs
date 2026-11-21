using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class KozakiKakeiFourNormalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normal-form carrier has exactly one element. The allowable permutation subgroup has eight elements and its permutation action on that carrier has singleton image.",
        H("The four-column normal-form space"),
        Blocks(
            Definition("fourNormal", "The unique four-column matrix",
                "Its rows are (0,1,1,1) and (−1,0,1,2)."),
            Theorem("normalized_four_iff", "Four-column singleton normal form",
                "The closing minor forces the last upper entry to be one, and the last consecutive minor forces the last lower entry to be two. The displayed matrix satisfies every nonvanishing and normalization condition."),
            Theorem("allowable_four_card", "Eight allowable column permutations",
                "The four rotations and four reflections correspond bijectively to a start column and a Boolean choice of orientation. Evaluation at zero determines the start and evaluation at one distinguishes the orientations. Each of the eight induces the identity on the one-point carrier."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static string NodeId(string name) =>
        "frieze-fournormal-" + name.ToLowerInvariant().Replace('_', '-');
}
