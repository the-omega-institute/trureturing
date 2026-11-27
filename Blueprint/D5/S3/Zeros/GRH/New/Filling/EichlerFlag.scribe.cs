using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class EichlerFlagDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eichler Flag", H("Eichler Flag"),
        Blocks(
            Paragraph(Text("Link of two frames, Gram discriminant g(γ); basis of the marked unimodular lattice. Abstract systems of positive kernels: products, semicontinuity, floor-by-floor sieve bound. Eichler maps along a frame vector lie in the Bessel unipotent group; character value.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/EichlerFlag.exists_mem_besselU_eq_eichlerMap"),
                H("exists_mem_besselU_eq_eichlerMap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let x = r∑_b j_b f_b with j_b = 0 for b ≥ a, and m = h(v, ·) vanish at f_b for b < a. The Eichler map 1 + x h(v, ·) − (v + τh(v,v)x) h(x, ·) is an element u of 𝖴 with σ(u) = r∑_b j_b m(f_{b+1}); f is the frame, σ = simpleRootSum, τ = TraceOne.τ has trace 1.")))))));
}
