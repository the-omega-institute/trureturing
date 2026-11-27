using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.QuotientMeasure;

internal sealed class UnimodularDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unimodular", H("Unimodular"),
        Blocks(
            Paragraph(Text("Proper actions have cutoff weights; discrete subgroups; unfolding a sum over a lattice. Covering radius of a subgroup at most n² over the first minimum of its dual. Quotient measure under equivariant measure-preserving maps and right translation. Groups with a lattice are unimodular; cocompact discrete subgroups have finite covolume.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/QuotientMeasure/Unimodular.exists_eq_smul_haar"),
                H("exists_eq_smul_haar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("On a second countable locally compact group with a Haar measure μ that is also right invariant, every s-finite right invariant measure ν is dμ for some d in [0, ∞].")))))));
}
