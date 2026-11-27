using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class FinitePartDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Part", H("Finite Part"),
        Blocks(
            Paragraph(Text("Finite part of the Weil representation: stable, smooth, vacuum characterised by lattice invariance.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/FinitePart.eventually_omega_eq_self"),
                H("eventually_omega_eq_self"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Vectors of the finite part are smooth: for f in 𝒲_f, ω(1,k)f = f for all k in a neighbourhood of 1 in the finite adelic unitary group.")))))));
}
