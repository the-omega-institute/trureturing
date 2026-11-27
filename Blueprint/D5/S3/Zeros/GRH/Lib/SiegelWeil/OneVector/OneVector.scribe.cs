using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.OneVector;

internal sealed class OneVectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One Vector", H("One Vector"),
        Blocks(
            Paragraph(Text("Siegel's mean value formula for representing one number by a sum of norms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/OneVector/OneVector.classSum_norm_eq"),
                H("classSum_norm_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Siegel's formula. Let n = |κ| ≥ 3, K ⊂ K₀ open, Φ₀ ≥ 0 K-invariant Schwartz–Bruhat, α = ᾱ totally positive. Then ∑_{x∈E^n, x*x=α} Φ₀(h⁻¹x) converges, and its K-class sum is (class sum of 1)·|D_E|^{1/4}·∏_v π^n α_v^{n−1}/(n−1)!·∫∫Φ₀(x)ψ_f(z(x*x−α)/2) dx dz, z = z̄ a finite adele, measures volÔ, volume_codifferent.")))))));
}
