using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseSOSDualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native SOS sufficiency and diagonal tensor duality", H("Native SOS sufficiency and diagonal tensor duality"), Blocks(
            Paragraph(Text("The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.")),
            Describe.Lean(DescribeId.Create("bosesosduality-even-sos-nonnegative"),
                DeclarationHandle.Create(Prefix + "even_sos_nonnegative"),
                H("Actual nonnegative trace pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("A homogeneous complex coherent symbol p of an actual Hermitian operator, with native SOS squared-variable expansion, pairs nonnegatively with every actual Bose-PPT matrix. Constructed PSD cut certificates have the same complex coherent symbol; polynomial separation proves equality of their symmetric compressions before trace pairing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bosesosduality-diagonal-dual-iff-sos"),
                DeclarationHandle.Create(Prefix + "diagonal_dual_iff_sos"),
                H("Exact diagonal operator SOS equivalence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("For occupation-diagonal Hermitian operators with actual real symbol p(X squared), membership in the actual Bose-PPT dual is equivalent to the native SOS condition. This supplies the operator-polynomial step in Gulati-Nechita-Park Theorems 8.9 and 8.11; BoseHierarchy uses it to prove the complete marginal and Parrilo hierarchy characterization."))), DescribeRole.Theorem))));
}
