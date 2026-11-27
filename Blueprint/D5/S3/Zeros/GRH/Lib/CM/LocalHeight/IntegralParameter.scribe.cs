using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.LocalHeight;

internal sealed class IntegralParameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral Parameter", H("Integral Parameter"),
        Blocks(
            Paragraph(Text("Exponential of formal series; Legendre bounds for valuations of factorials. Normalised CM cubic has unit discriminant at every prime; ultrametric bounds. Local height of the curve; Tate's trick under torsion translation and isogeny. Rings of integral power series in a parameter; stability for the curve's parameter.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/LocalHeight/IntegralParameter.deriv_mem_phiSeriesRing"),
                H("deriv_mem_phiSeriesRing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The ring 𝔬[[φ]] of integral power series in φ, viewed as series in z over ℂ_p, is stable under d/dz.")))))));
}
