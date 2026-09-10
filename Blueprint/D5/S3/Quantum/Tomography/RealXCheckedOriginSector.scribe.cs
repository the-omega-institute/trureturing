using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class RealXCheckedOriginSectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete rational forest excludes simultaneous small residuals on a proper signed-Cayley sector of the actual real-X seed.",
        H("A Complete Checked Origin-Sector Traversal"),
        Blocks(Describe.Lean(
            DescribeId.Create("real-x-complete-origin-sector-sublevel-exclusion"),
            DeclarationHandle.Create("D5/S3/Quantum/Tomography/RealXCheckedOriginSector.no_common_unbiased_sublevel_in_checked_origin_sector"),
            H("No six-residual near-zero occurs in the stated five-dimensional sector"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The statement displays the exact seed matrix over Q(i,sqrt(21)) and the dephased signed-Cayley vector. Each of the five free real parameters lies in [-1/5,1/5]. The conclusion excludes simultaneous absolute residuals at most 1/64 for all six outcomes.")),
                Paragraph(Text("The finite source contains 237 ordered nodes: 119 interval-expression exclusions and 118 closed splits. Every numerical annotation is independently rechecked, both split halves are retained, and each leaf expression must have the specified residual syntax. A separate identity relates that syntax to the actual conjugate-transpose measurement. No local enclosure or global cover is supplied as a premise.")),
                Paragraph(Text("This is an integration instance on a proper subregion of chart zero, not the full 32-chart cover or a new Hadamard neighborhood exclusion. The proof script requests kernel reduction of the literal check, but local Lean elaboration has not been executed. Existing Krawczyk contraction records still need their own executable proof adapter."))),
            DescribeRole.Theorem))));
}
