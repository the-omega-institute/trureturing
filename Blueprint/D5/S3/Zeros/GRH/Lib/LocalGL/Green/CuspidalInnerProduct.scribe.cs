using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class CuspidalInnerProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cuspidal Inner Product", H("Cuspidal Inner Product"),
        Blocks(
            Paragraph(Text("Naming characters of F_Q^× by field elements; multiplicativity and norm compatibility. Cuspidal character times Steinberg is induced from the Coxeter torus.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalInnerProduct.rankInner_greenCuspidal_mulMu"),
                H("rankInner_greenCuspidal_mulMu"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a finite extension L of k embedded by φ in K, the inner product on GL_{[L:k]}(k) of C_η with B·μ is the mean over z ∈ L^× of conj η(φz) times B at multiplication by z.")))))));
}
