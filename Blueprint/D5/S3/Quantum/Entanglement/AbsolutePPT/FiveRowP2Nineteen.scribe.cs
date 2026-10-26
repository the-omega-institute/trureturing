using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;
internal sealed class FiveRowP2NineteenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dimension-nineteen estimate holds throughout the real concentration interval. Three quartic certificates and the scalar constraints control the low and middle parameter regions.", H("FiveRowP2Nineteen"), Blocks(
            Paragraph(Text("The dimension-nineteen estimate holds throughout the real concentration interval. Three quartic certificates and the scalar constraints control the low and middle parameter regions.")),
            Describe.Lean(DescribeId.Create("fiverowp2nineteen-concentrated-nineteen"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Nineteen.concentrated_nineteen"),
                H("concentrated nineteen"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem concentrated_nineteen (r H D a q s j : ℝ) (h : Hyp r H D a q s) (hj : 10 ≤ j) (hj' : j ≤ 80) : energy 95 j r H D a q ≤ (5/456)*(mass 95 j r H D)^2"))), DescribeRole.Theorem)
        )));
}
