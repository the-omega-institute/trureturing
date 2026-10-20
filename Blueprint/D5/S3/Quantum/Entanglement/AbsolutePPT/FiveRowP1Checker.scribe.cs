using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class FiveRowP1CheckerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Soundness of finite rational covers for the scalar inequalities.",
        H("FiveRowP1Checker"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiverowp1checker-check"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Checker.check"),
                H("All local checks and complete postorder traversal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each accepted forest retains both closed halves at every split. Infeasibility uses strict upper bounds, whereas target bounds are nonstrict. Endpoint derivative signs and the quadratic vertex cover the continuous real interval of j; the generic local-step cover theorem assembles the leaves."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fiverowp1checker-checked-scalar-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Checker.checked_scalar_bound"),
                H("Existing finite cover theorem consumes exact local checks"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each accepted forest retains both closed halves at every split. Infeasibility uses strict upper bounds, whereas target bounds are nonstrict. Endpoint derivative signs and the quadratic vertex cover the continuous real interval of j; the generic local-step cover theorem assembles the leaves."))), DescribeRole.Theorem))));
}
