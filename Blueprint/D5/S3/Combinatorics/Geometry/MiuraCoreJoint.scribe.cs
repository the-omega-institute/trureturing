using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreJointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreJoint.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting contractions on one actual rectangle.", H("Commuting contractions on one actual rectangle"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracorejoint-0"),
                DeclarationHandle.Create(Prefix + "contractRow"), H("Signed deletion along the row axis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Row contraction is column contraction of the actual transpose followed by transposition back."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorejoint-1"),
                DeclarationHandle.Create(Prefix + "frozen_row_after_column"), H("A frozen row remains legal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtracting one common column slope from each cell to the right of the deleted column preserves the frozen-row second-difference equations at every surviving column."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorejoint-2"),
                DeclarationHandle.Create(Prefix + "frozen_column_after_row"), H("A frozen column remains legal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same preservation law with exchanged axes retains each original frozen column after row contraction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorejoint-3"),
                DeclarationHandle.Create(Prefix + "contract_row_column_commute"), H("The two deletion orders agree exactly"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual row and column satisfying their frozen equations, both successive signed contractions are legal and yield equal integer-valued functions on the same smaller rectangle. The origin-adjacent slope of either operation is unchanged by the other operation; the two corrections add."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorejoint-4"),
                DeclarationHandle.Create(Prefix + "contractRow_residual"), H("Row contraction preserves the residual class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A legal signed row deletion preserves normalization, each exact extremum count, and the predicate that the minima are contained in no single common physical side."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorejoint-5"),
                DeclarationHandle.Create(Prefix + "JointReduction"), H("Chains on successive actual arrays"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each column or row step deletes one of two consecutive genuinely frozen lines. Its output is the actual input of the remaining chain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorejoint-6"),
                DeclarationHandle.Create(Prefix + "residual_joint_bounded_core_exists"), H("Both finite bounds hold on one residual array"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive a and b, a residual array on a rectangle with at least two cells per axis admits an actual joint deletion chain to a residual array with each dimension between 2 and 2(a+b)-1. Column reduction followed by transposed column reduction gives the same bounded target object. This is an existence result and does not assert uniqueness."))), DescribeRole.Theorem))));
}
