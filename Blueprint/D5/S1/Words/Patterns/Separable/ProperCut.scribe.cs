using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class ProperCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/Separable/ProperCut.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/fu2019two");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual classical 2413/3142 avoidance implies a nonempty proper direct or skew cut.",
        H("Classical avoidance and a proper cut"),
        Blocks(
            Paragraph(Text(
                "This is the known classical bridge recorded "
                + "in Proposition 2.1 of the cited source, with an internal graph proof. "
                + "It does not settle the real-rootedness assertion in Conjecture 5.2.")),
            Node("pattern2413", "The literal pattern 2413", DescribeRole.Definition,
                "The values are 1, 3, 0, 2 at the four increasing zero-based positions."),
            Node("pattern3142", "The literal pattern 3142", DescribeRole.Definition,
                "The values are 2, 0, 3, 1 at the four increasing zero-based positions."),
            Node("avoidance_proper_cut", "A nonempty proper direct or skew cut", DescribeRole.Theorem,
                "Contains is the unchanged order-embedding predicate from "
                + "DerangementRatioNonconvergence. An induced four-vertex path in the inversion "
                + "graph supplies one of the two forbidden patterns. A maximal disconnected "
                + "induced subset proves that the graph or its complement is disconnected. "
                + "A boundary dart makes the root component order-convex, and its least omitted "
                + "position supplies the cut with the displayed strict value inequalities."),
            Paragraph(Text(
                "Real-rootedness of the actual-avoider descent polynomials remains unproved here. "
                + "The source's tree bijection "
                + "requires the greatest valid cut, standardization, preservation of actual "
                + "avoidance, and descent correspondence. Those conclusions and the "
                + "real-rootedness proof are not supplied by this existence theorem.")))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);
}
