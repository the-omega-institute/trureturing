using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.NumberTheory;

internal sealed class FundamentalDomainsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fundamental Domains", H("Fundamental Domains"),
        Blocks(
            Paragraph(Text("Fundamental domains and covolumes of adelic lattices; box domain for filtered discrete subgroups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/NumberTheory/FundamentalDomains.exists_fundamental_domain_im_skew"),
                H("exists_fundamental_domain_im_skew"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For E stably unramified and nonzero reals t_v, the group of vectors (t_v Im Φ_v(s))_v, s an integer of E with s̄ = −s, has a measurable fundamental domain in ℝ^(infinite places) of volume ∏|t_v|·√|disc E⁺|.")))))));
}
