using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseSOSCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSCertificates.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PSD cut certificates for even homogeneous SOS forms", H("Actual PSD cut certificates for even homogeneous SOS forms"), Blocks(
            Paragraph(Text("The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.")),
            Describe.Lean(DescribeId.Create("bosesoscertificates-term-cut-certificate"),
                DeclarationHandle.Create(Prefix + "term_cut_certificate"),
                H("Rank-one tensor cut certificate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("A homogeneous term X^alpha q(X)^2, with degree(alpha)+2j=r, is represented by a genuine rank-one PSD tensor matrix after a concrete prefix partial transpose. Tensor words are chosen from the actual occupation representatives; no operator certificate is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bosesoscertificates-even-form-cut-certificates"),
                DeclarationHandle.Create(Prefix + "even_form_cut_certificates"),
                H("Full native even SOS certificate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("Every homogeneous degree-r form whose squared-variable expansion is a native real SOS has a finite sum of actual PSD partial-transpose tensor certificates. This constructs the sufficiency argument of Gulati-Nechita-Park Theorem 8.11, for all degrees and dimensions, including zero terms."))), DescribeRole.Theorem))));
}
