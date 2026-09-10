using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport.Thermodynamics;

internal sealed class ResetHeatBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit heat balance bounds the entropy removed by reset.",
        H("Reset Heat Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reset-heat-bound"),
                DeclarationHandle.Create("D5/S3/DivergenceSupport/Thermodynamics/ResetHeatBound.reset_heat_bound"),
                H("Reset Heat Bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write the memory entropy change as minus erasedEntropy. If beta times heat equals erasedEntropy plus mutualInfo plus divergence, with both remainders nonnegative, the existing Landauer balance bound gives erasedEntropy at most beta times heat.")),
                    Paragraph(Text("All quantities are real numbers and the exact balance is a hypothesis. For a thermodynamic application, beta must represent positive inverse temperature, heat must use the reservoir sign convention, and entropy units must be compatible. The theorem does not derive that physical interpretation, the balance itself, or a universal minimum cost for every operation called forgetting."))),
                DescribeRole.Theorem))));
}
