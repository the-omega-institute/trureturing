using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PointDeletedSteinerSwitchDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting a point from a complete Steiner system leaves a matching. A path replacement controls the first deficit.",
        H("Switches in Point-Deleted Steiner Systems"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("point-deleted-family"),
                DeclarationHandle.Create(Module + ".pointDeletedFamily"),
                H("The retained packing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Keep exactly the original blocks avoiding the distinguished point, using the complementary embedding to label the remaining points."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("switched-packing"),
                DeclarationHandle.Create(Module + ".switchedPacking"),
                H("The two-block switch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the path in order a,b,v,d,c remove the blocks abv and vdc, then add avc."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("switched-leave"),
                DeclarationHandle.Create(Module + ".SwitchedLeave"),
                H("The matching and path in the leave"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Keep the matching edges away from the two path endpoints, and include exactly the four successive path edges."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("point-deleted-switch"),
                DeclarationHandle.Create(Module + ".point_deleted_switch"),
                H("Maximality after a point-deleted switch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any complete Steiner triple system and any distinguished point, the retained packing has exactly a fixed-point-free involution m as its leave. For any a and v with v distinct from a and m(a), put c=m(a). The retained pairs av and cv have completions b and d.")),
                    Paragraph(Text("The switched family keeps pair uniqueness and has one fewer block. Its leave replaces ac by the path a,b,v,d,c. The remaining matching has at most one edge between any vertex and the rest. A triangle must therefore use two successive path edges. Only the two interior vertices b and d can be joined by a remaining matching edge, because a and c were paired to each other. The switch is maximal exactly when d is not m(b)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matching-switch-first-deficit"),
                DeclarationHandle.Create(Module + ".matching_switch_first_deficit"),
                H("One fewer block than the largest saturated extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a positive row dimension, and fix the lifted cross-row family with distinct rows, pair uniqueness and zero-sum completion of every cross-row pair. As in the classwise decomposition, normalize at zero and preserve dimension one more than the row dimension. Suppose the residue labels have a packing whose leave is a perfect matching, together with two blocks giving a successful switch of the described shape.")),
                    Paragraph(Text("In that packing each label has exactly one unused partner and every block through a label uses two partners. Thus the label count r is even. Every other packing has at least one unused partner at every label, so the matching packing attains the upper bound r(r−2)/6. This count times the number of actual residue classes, plus the rowwise Latin cells, bounds every compatible extension. A saturated extension attains that bound. A successful switch in one class realizes one fewer.")),
                    Paragraph(Text("For the classical local spectrum see Colbourn, Rosa and Znám (https://doi.org/10.1007/BF01388482). The criterion here concerns the specified local switch on the input system and its effect on the dimension-preserving extension."))),
                DescribeRole.Theorem))));
}
