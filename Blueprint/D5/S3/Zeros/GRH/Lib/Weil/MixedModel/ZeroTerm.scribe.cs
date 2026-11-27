using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class ZeroTermDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero Term", H("Zero Term"),
        Blocks(
            Paragraph(Text("Splittings along isotropic subspaces, Levi and unipotent radical of the parabolic, adapted points. Heisenberg law in split coordinates; real vacuum becomes the Gaussian of the mixed model. Finite vacuum and Schwartz-Bruhat data in the mixed model: partial Fourier transform. Zero term and mixed Schrödinger model; theta expansion; vacuum is Gaussian times lattice indicator.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/ZeroTerm.mixedTerm_omega_vacElem"),
                H("mixedTerm_omega_vacElem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If g is adapted to t in the splitting D, there is c ≠ 0 with (ω(g)vac)[x] = c·|e(t*x)|²·vac, the vacuum of V₀, for all x in 𝔸^p; here f[x] is the mixed model and e = vacuumFn.")))))));
}
