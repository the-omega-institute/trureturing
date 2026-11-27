using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Descent;

internal sealed class ReductionModPDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduction Mod P", H("Reduction Mod P"),
        Blocks(
            Paragraph(Text("p-adic tests, their tilts, Witt and completion functors, base change of coefficients. Locally constant functions on Spec, flatness over Bezout domains, torsion-free tensors, Witt vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Descent/ReductionModP.witt_reduction_spec"),
                H("witt_reduction_spec"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let S be a perfect algebra over a domain M of characteristic p. Then the zeroth coordinate W(S) → S is reduction modulo p, W(S) is p-torsion-free and p-complete, and x lies in p^k W(S) exactly when its first k coordinates vanish.")))))));
}
