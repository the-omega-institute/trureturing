using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Descent;

internal sealed class VDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "V Descent", H("V Descent"),
        Blocks(
            Paragraph(Text("v-covers of perfect rings descend: follow a class by Zorn to a valuation ring.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Descent/VDescent.isCover_of_points"),
                H("isCover_of_points"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Almost v-descent: let π kill N. If y: b → b' of perfect O^♭-algebras makes Hom(b', S^♭) → Hom(b, S^♭) onto for all p-adic tests S, then on perfect D, h_b and the image of h_{b'} have the same cohomology for D ⊗ N ⊗ 𝔪.")))))));
}
