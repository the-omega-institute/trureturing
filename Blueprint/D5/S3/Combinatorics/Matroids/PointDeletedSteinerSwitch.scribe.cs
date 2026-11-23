using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PointDeletedSteinerSwitchDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting a point from a finite complete Steiner system leaves a matching. A path replacement controls the first deficit.",
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
                    Paragraph(Text("For any finite complete Steiner triple system and any distinguished point, the leave of the retained packing is exactly the perfect matching defined by a fixed-point-free involution m. For any a and v with v distinct from a and m(a), put c=m(a). The retained pairs av and cv have completions b and d. The five vertices a,b,v,d,c are pairwise distinct.")),
                    Paragraph(Text("Remove the blocks abv and vdc and insert avc. The switched family keeps pair uniqueness and has one fewer block. Its leave keeps every other matching edge and replaces ac by the path a,b,v,d,c. The remaining matching has at most one edge between any vertex and the rest. A triangle must therefore use two successive path edges. The only possible leave triangle is b,v,d, since the other two-edge subpaths have a or c as an endpoint and ac was removed from the matching. This triangle occurs exactly when d = m(b). An additional block can be inserted exactly when the leave contains a triangle, so the switch is maximal exactly when d is not m(b)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matching-switch-first-deficit"),
                DeclarationHandle.Create(Module + ".matching_switch_first_deficit"),
                H("One fewer block than the largest saturated extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a positive row dimension d, and fix the lifted cross-row family with distinct rows, pair uniqueness and zero-sum completion of every cross-row pair. As in the classwise decomposition, normalize at zero and preserve dimension one more than the row dimension. Suppose the residue labels have a packing whose leave is a perfect matching, together with two blocks giving a successful switch of the described shape.")),
                    Paragraph(Text("In that packing each label has exactly one unused partner and every block through a label uses two partners. Thus the label count r is even. Every other packing has at least one unused partner at every label, so the matching packing attains the upper bound r(r−2)/6. Multiplying the packing bound by the 3^(d+1) actual residue classes and adding the 3^d r^2 rowwise Latin cells gives the cap N = 3^d r^2 + 3^(d+1) floor(r(r−2)/6) on the number of internal blocks in every compatible extension. Using the matching packing in every class yields a saturated extension of size N. A successful switch in one class yields a saturated extension of size N−1.")),
                    Paragraph(Text("For the classical local spectrum see Colbourn, Rosa and Znám (https://doi.org/10.1007/BF01388482). The criterion here concerns the specified local switch on the input system and its effect on the dimension-preserving extension."))),
                DescribeRole.Theorem))));
}
