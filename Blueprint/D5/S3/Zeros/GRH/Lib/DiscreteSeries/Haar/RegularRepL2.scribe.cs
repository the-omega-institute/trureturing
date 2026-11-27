using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar;

internal sealed class RegularRepL2Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular Rep L2", H("Regular Rep L2"),
        Blocks(
            Paragraph(Text("Polynomial volume growth of norm balls in closed subgroups; integrability of norm powers. Right regular representation on L² of U(p,q) is continuous and unitary.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/RegularRepL2.integral_decay_le"),
                H("integral_decay_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let j : S → U(J) be a proper group homomorphism, J a hermitian involution of size n ≥ 1, ν right invariant, finite on compacts, c > 8n² natural, y∈U(J). Then (2/‖j(s)y‖)^c is ν-integrable with integral ≤ 16^c·ν{‖j(s)−1‖ ≤ 1} (operator norms).")))))));
}
