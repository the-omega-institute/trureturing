using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class SupportColumnZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supports with least column 0.",
        H("Supports with least column 0"), Blocks(
            Describe.Lean(DescribeId.Create("appt-quadbit-supportcolumnzero"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SupportColumnZero.valid00"),
                H("Supports with least column 0"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The least selected column ranges from 0 through 0. The block sizes are 816. Each table " +
                    "retains its supplied witness for every strictly increasing four-column support. The valid " +
                    "proofs establish CaseValid for every table entry. The align proofs identify the ordered " +
                    "entry list with all increasing four-tuples having that least column. These equalities " +
                    "connect table checking to complete support coverage, including mixed signs, both " +
                    "orientations, and zero cofactors."))), DescribeRole.Theorem),
            Paragraph(Text("These statements concern real scalar spectra and finite cofactor certificates. Connecting " +
                    "the boundary inequalities to a physical APPT model, constructing an attaining state, and " +
                    "determining a purity supremum require additional results.")))));
}
