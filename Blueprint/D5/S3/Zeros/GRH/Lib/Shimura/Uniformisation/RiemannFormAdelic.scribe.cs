using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class RiemannFormAdelicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Riemann Form Adelic", H("Riemann Form Adelic"),
        Blocks(
            Paragraph(Text("Ball and fibre spaces; E⊗R acts complex-linearly through a period map. Model: an integral tower of Kuga–Sato varieties with covers and Hecke legs. Riemann form on rational vectors as a trace and via the adelic character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/RiemannFormAdelic.fourierChar_polarisationForm"),
                H("fourierChar_polarisationForm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If gᴴβg = a·1 with a a finite adele, then exp(2πi ∑_v 2 Re Φ_v(ξ zᴴβy)) = ψ_f(a ξ (g⁻¹z)ᴴ(g⁻¹y)) for all y, z in Eⁿ, with ξ from the datum D.")))))));
}
