using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate;

internal sealed class HodgeTateMapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hodge Tate Map", H("Hodge Tate Map"),
        Blocks(
            Paragraph(Text("Hodge–Tate map in weight h: definition, naturality, scaling, multiplicativity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTateMap.hodgeTateMap_cup"),
                H("hodgeTateMap_cup"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Product formula: for Hodge classes x of degree a and y, λ_l(x × y) = ∑_{h ≤ l} C(l,h)(−1)^{(a+h)(l−h)} λ_h(x) × λ_{l−h}(y).")))))));
}
