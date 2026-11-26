using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class ThetaFunctionalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Functional", H("Theta Functional"),
        Blocks(
            Paragraph(Text("The finite-adelic cocycle of the Weil operators written as a finite Gauss sum. Finite cocycle is trivial: metaplectic cover splits over the finite-adelic unitary group. Adelic multiplier, vacuum measure; the cocycle is trivial on the adelic unitary group. Existence and uniqueness of the invariant theta functional; Poisson-type sum over rational points.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/ThetaFunctional.eq_smul"),
                H("eq_smul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If θ is a theta functional of V, every bounded functional ℓ on 𝒮(V) invariant under the Heisenberg operators ϱ(γ), γ a rational point of V, is a complex multiple of θ.")))))));
}
