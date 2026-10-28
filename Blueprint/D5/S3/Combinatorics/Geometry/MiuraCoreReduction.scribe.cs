using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreReduction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded-width reduction follows the original actual array.", H("Finite one-axis core reduction"),
        Blocks(
            Describe.Lean(DescribeId.Create("miura-column-reduction"),
                DeclarationHandle.Create(Prefix + "ColumnReduction"), H("A chain of actual signed deletions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reflexive relation starts at the given array. Each further step deletes one of two consecutive genuinely frozen columns using its actual signed slope. The target of that deletion is exactly the source of the remaining chain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miura-residual-column-core"),
                DeclarationHandle.Create(Prefix + "residual_column_core_exists"), H("A bounded-width residual from the same array"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive split a,b, nonempty row axis, and residual array with at least two columns, there is an actual residual array of width between 2 and 2(a+b)-1 connected to it by a finite chain of signed frozen deletions. Strong induction on width applies the consecutive-frozen-column bound and the exact residual-preservation theorem at every step. This establishes existence of a related bounded-width array; uniqueness of a reduced core and the joint expansion fibers require further arguments."))), DescribeRole.Theorem))));
}
