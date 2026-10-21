using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class FiveRowP1Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full five-row scalar upper bound in dimensions five through eighteen.",
        H("FiveRowP1"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiverowp1-scalar-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound"),
                H("All dimensions five through eighteen, both branches, every real j"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n from 5 through 18 and every real j in [10,5*n-15], the stated scalar hypotheses imply energy <= ((5*n+8)/(5*n+2)^2) times squared mass. Both tail branches are covered for each N=5*n. Deriving these hypotheses from literal APPT, assigning the spectral variables, and transferring the scalar result to the physical theorem require separate arguments."))), DescribeRole.Theorem))));
}
