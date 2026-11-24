using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerAlternatingSwitchesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Large alternating components identify all successful starts in a point-deleted Steiner system.",
        H("Alternating Components and Maximal Steiner Switches"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pivot-matchings"),
                DeclarationHandle.Create(Module + ".pivotMatchings"),
                H("The two pivot matchings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the matching translations for the deleted point and for the fixed remaining pivot."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("successful-start"),
                DeclarationHandle.Create(Module + ".SuccessfulStart"),
                H("A successful starting label"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pivot differs from the start and its leave partner. The blocks completing the two pairs with the pivot have third labels that are not leave partners of one another."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("successful-starts"),
                DeclarationHandle.Create(Module + ".point_deleted_successful_starts"),
                H("All successful starting labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Delete any point from a finite complete Steiner triple system on r+1 points. The remaining family is a partial Steiner system and has a leave partner map m. For every retained pivot, the embedding of its successful starts into the enlarged point set is exactly the set of vertices in matching components of size at least six. If four divides r, there are at least six such starting labels for every pivot.")),
                    Paragraph(Text("The square containing the adjoined point also contains the deleted point, the retained pivot, and its leave partner. All vertices outside the square are eligible retained starts. Pair completion gives the two switch blocks. Their switch is successful exactly where the translations disagree in the two orders. The enlarged carrier has r+2 points, so divisibility of r by four forces a large component."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-deficit"),
                DeclarationHandle.Create(Module + ".point_deleted_first_deficit_of_four_dvd"),
                H("The first deficit without a switch hypothesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix positive row dimension d and nonzero residue modulus 3r. Suppose the lifted cross-row family has pair completion, distinct rows, and pair uniqueness. If a complete Steiner system exists on r+1 points and four divides r, the largest internal extension has size N equal to 3^d r^2 plus 3^(d+1) times floor(r(r−2)/6). There are saturated internal extensions of sizes N and N−1, and every internal extension has size at most N.")),
                    Paragraph(Text("Choose a successful start at any retained pivot and apply the one-class switch construction. The matching packing supplies the upper bound in every class."))),
                DescribeRole.Theorem))));
}
