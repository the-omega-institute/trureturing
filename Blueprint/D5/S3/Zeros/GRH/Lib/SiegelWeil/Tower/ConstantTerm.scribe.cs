using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.Tower;

internal sealed class ConstantTermDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant Term", H("Constant Term"),
        Blocks(
            Paragraph(Text("Constant term of a theta integral along an isotropic line, unfolded over orbits.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/ConstantTerm.exists_unfold_constant_term"),
                H("exists_unfold_constant_term"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Unfolding: for some real c ≠ 0, if the term x = 0 vanishes, ∫_{[U(V′)]} Σ_x constTermAt x (ω(g,h)f) dh is c times the integral of |t|^(rk V+1) Σ_{ξ∈E^×} θ(lineTerm) over ideles mod E^×, [U(V)] and the maximal compact subgroup, when this integrand is integrable.")))))));
}
