using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class RelativeChainsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative Chains", H("Relative Chains"),
        Blocks(
            Paragraph(Text("Relative cohomology of pairs of functors; locally zero sections, excision, transfer.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/RelativeChains.excision"),
                H("excision"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Excision: if u: V' → V is a monomorphism and u(V') ∪ U is dense in V for the coefficient F, then ℤ[V']/ℤ[u⁻¹U] → ℤ[V]/ℤ[U] induces bijections on Ext^n(·, F) for all n.")))))));
}
