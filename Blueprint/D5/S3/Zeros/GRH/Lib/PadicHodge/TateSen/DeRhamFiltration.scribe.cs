using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.TateSen;

internal sealed class DeRhamFiltrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "De Rham Filtration", H("De Rham Filtration"),
        Blocks(
            Paragraph(Text("Filtration of B_dR by powers of t; Galois invariants of B_dR modulo submodules.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/TateSen/DeRhamFiltration.exists_sub_mem_of_smul_sub_mem"),
                H("exists_sub_mem_of_smul_sub_mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let j have open image in G_p, cutting out the local field K, and let S be a B_dR^+-submodule of B_dR. If j(g)x − x lies in S for all g, then x − a lies in S for some a in K.")))))));
}
