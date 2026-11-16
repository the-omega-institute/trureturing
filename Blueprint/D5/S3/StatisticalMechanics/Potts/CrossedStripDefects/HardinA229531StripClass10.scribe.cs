using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects;
internal sealed class HardinA229531StripClass10Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass10.";
    private const string Note = "D5/L/SpinModels/hardin2013a229531";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact width-five HDA transfer.", H("Width-five HDA transfer"), Blocks(
            Describe.Lean(DescribeId.Create("transition-counts"), DeclarationHandle.Create(Prefix + "transition_counts"),
                H("Exact successor count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For every actual row p : Fin 5 to Fin 3 and residual d : Fin 2 satisfying Valid, the number of successor rows r whose horizontal and cross-bond defects fit d and whose new residual class is 10 equals T (cl p d) 10. Finite kernel evaluation checks this exact column of the 20 by 20 transfer. The combined successor identity applies this column in its corresponding target case."))), DescribeRole.Theorem))));
}
