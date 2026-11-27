using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class ZeroTermLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero Term Law", H("Zero Term Law"),
        Blocks(
            Paragraph(Text("Parabolic subgroup acts on the zero term by an explicit character of the determinant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/ZeroTermLaw.zeroTerm_omega"),
                H("zeroTerm_omega"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If gk = ka with a in GL_p(𝔸) and gι = ιg₀ + kc with g₀ in the adelic group of V₀, then ev(ω(g)f) = υ(det a)⁻¹ |det a|^{1/2} ω(g₀) ev(f) for all f.")))))));
}
