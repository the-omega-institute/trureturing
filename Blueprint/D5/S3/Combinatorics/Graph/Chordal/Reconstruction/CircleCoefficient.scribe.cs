using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal.Reconstruction;

internal sealed class CircleCoefficientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circle-supported gains on finite powers of paths have uniform coefficient one for reconstruction with unrestricted unit-quaternion potentials.",
        H("Circle gains on finite power paths"),
        Blocks(
            Result("powerPath-circle-coefficient-one", "powerPath_circle_coefficient_one", "Uniform ambient upper bound",
                "At every finite path order and width, circle-supported gains can be fitted in the full round unit-quaternion group with error at most the triangle-defect budget.",
                "Below half pi, principal triangle angles satisfy the four-face identity and lift to real edge gains. For larger defects, consecutive clique blocks alternate between two orthogonal quaternion lines."),
            Result("sharpGain-exact-defect", "sharpGain_exact_defect", "Defect of the squared-path example",
                "The explicit signed squared-path gains have triangle defect exactly pi divided by four times the length parameter.",
                "Each increasing triangle contains two unit steps and a step of length two. Their signed angles add to one of the two principal angles of the same magnitude."),
            Result("sharpGain-ambient-lower", "sharpGain_ambient_lower", "Ambient cycle obstruction",
                "Every full unit-quaternion potential on the squared-path example has a maximum edge error at least the triangle defect times the length parameter divided by one plus that parameter.",
                "The cycle through the even vertices and back through the odd vertices has round holonomy half pi. The product triangle inequality bounds that holonomy by the cycle length times the fitting error."),
            Result("admissible-iff-one-le", "admissible_iff_one_le", "Exact uniform coefficient",
                "A real number is a uniform ambient coefficient for circle gains on finite powers of paths exactly when it is at least one.",
                "The uniform upper construction gives sufficiency. The squared-path lower bounds tend to one as the length parameter grows."))));

    private static DocumentBlock.Describe Result(string id, string declaration, string heading,
        params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()), DescribeRole.Theorem);
}
