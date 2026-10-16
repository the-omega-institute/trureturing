using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class FullRowCofactorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered full-row cofactors.",
        H("Ordered full-row cofactors"), Blocks(
            Describe.Lean(DescribeId.Create("appt-quadbit-fullrowcofactor"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/FullRowCofactor.cofactor_candidate_ordered_full"),
                H("Ordered full-row cofactors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let B be a real m-by-n matrix whose columns span the whole m-dimensional row space. A " +
                    "nonzero vector satisfying exact cofactorCandidates membership, including all original " +
                    "kernel equations, is a positive multiple of one orientation of an ordered full-row " +
                    "cofactor. The original nonnegative kernel equations are preserved for every row. A nonzero " +
                    "deleted minor supplies independent columns; extending these columns to a basis and sorting " +
                    "their indices gives a support of size m+1. Distinct indices remain distinct even when " +
                    "column values agree. The cofactor cross identity fixes the orientation and positive scale, " +
                    "including zero coordinates."))), DescribeRole.Theorem),
            Paragraph(Text("These statements concern real scalar spectra and finite cofactor certificates. Connecting " +
                    "the boundary inequalities to a physical APPT model, constructing an attaining state, and " +
                    "determining a purity supremum require additional results.")))));
}
