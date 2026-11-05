using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BosePPTDualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native SOS necessity for actual Bose-PPT dual operators", H("Native SOS necessity for actual Bose-PPT dual operators"), Blocks(
            Paragraph(Text("The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.")),
            Describe.Lean(DescribeId.Create("bosepptduality-bose-space"),
                DeclarationHandle.Create(Prefix + "boseSpace"),
                H("Actual Bose support space"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("The real Hermitian subspace is defined by the original full tensor-projector sandwich. Positivity is not imposed by the subspace."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosepptduality-bose-ppt"),
                DeclarationHandle.Create(Prefix + "bosePPT"),
                H("Actual all-cut Bose-PPT cone"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("The actual full Bose sandwich is combined with product-basis PSD partial transposes at every cut, including empty and full cuts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosepptduality-dual-bose-ppt-real-sos"),
                DeclarationHandle.Create(Prefix + "dual_bosePPT_real_sos"),
                H("SOS necessity without dropping closure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("Every Hermitian operator with nonnegative trace pairing against all actual Bose-PPT matrices has a native real SOS coherent polynomial. The proof uses closedness of the actual homogeneous SOS coefficient cone and finite-dimensional bipolarity. It does not identify an unclosed operator dual sum."))), DescribeRole.Theorem))));
}
