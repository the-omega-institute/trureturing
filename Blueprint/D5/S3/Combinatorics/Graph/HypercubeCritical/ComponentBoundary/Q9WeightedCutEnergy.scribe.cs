using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9WeightedCutEnergyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directional energy of a balanced cube support",
        H("Directional energy of a balanced cube support"),
        Blocks(
            Paragraph(Text("In the nine-cube, coordinate flips generate the translation group. Their Huang-signed lifts square to the identity and anticommute in distinct directions. The central sign in this action forces the square of the weighted sum of the lifts to be the sum of the squared weights times the identity. On a balanced support, changing signs at the vertices transfers the signed edge correlations to ordinary edge correlations. This yields a joint constraint on cut sizes for Hong–Wu–Xia Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2")),
            Describe.Lean(DescribeId.Create("joint-directional-correlation"),
                DeclarationHandle.Create(Module + ".sum_sq_direction_correlation_le"),
                H("Balanced supports bound the joint edge correlations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real vector supported on the balanced set, choose each weight to be the corresponding directional correlation after switching. Cauchy–Schwarz then bounds the sum of the squared correlations by the squared total mass."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-shore-directional-energy"),
                DeclarationHandle.Create(Module + ".cut_direction_energy"),
                H("Cut shores jointly constrain their edge directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a test vector taking constant values on the two shores. Each correlation splits into the two internal endpoint counts and twice the crossing count. Varying the constants tests all directions simultaneously."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cut-direction-discriminant"),
                DeclarationHandle.Create(Module + ".cut_count_discriminant"),
                H("Uniform direction counts force a nonpositive cut discriminant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cubic degree sum and uniform direction counts cancel the terms of highest degree. The remaining real quadratic must be nonnegative for every value of the sum of the two test constants when their difference is one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nine-crossing-shore-capacity"),
                DeclarationHandle.Create(Module + ".cut_shore_capacity_of_nine_crossings"),
                H("Missing directions bound the shore order of a nine-edge cut"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a 90-vertex balanced cubic count profile, suppose exactly three directions cross the cut, with three crossing edges in each. Completing the square after separating the crossing and noncrossing directions bounds an odd shore at 31 vertices if it lacks a noncrossing internal direction and at 39 if it lacks a crossing internal direction. The estimate uses the signed coordinate action and the two-shore counts."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedBoundaryGram")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells"))]));
}
