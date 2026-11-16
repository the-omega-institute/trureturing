using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects;
internal sealed class HardinA229531StripClassesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClasses.";
    private const string Note = "D5/L/SpinModels/hardin2013a229531";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact width-five HDA transfer.", H("Width-five HDA transfer"), Blocks(
            Describe.Lean(DescribeId.Create("transition-counts"), DeclarationHandle.Create(Prefix + "transition_counts"),
                H("All target classes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For every actual row p, residual d : Fin 2 and target s : Fin 20, Valid p d implies that the actual permitted successor sum is T (cl p d) s. Each target case directly applies its checked class theorem; the final recurrence consumes the combined identity."))), DescribeRole.Theorem))));
}
