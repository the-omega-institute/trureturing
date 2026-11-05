using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseLDUIDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Dicke and LDUI coordinates", H("Exact Dicke and LDUI coordinates"), Blocks(
            Paragraph(Text("The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.")),
            Describe.Lean(DescribeId.Create("boseldui-coordinates"),
                DeclarationHandle.Create(Prefix + "coordinates"),
                H("Exact upper-triangular Y to symmetric P"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("The diagonal coordinate is P_ii=Y_ii and each off-diagonal coordinate is P_ij=Y_min(i,j),max(i,j)/2. Substituting into ldui recovers the original upper-triangular normalized Dicke mixture: the off-diagonal weight 2P_ij cancels this factor one half. This is a direct application of the two definitions and is checked with the star criterion rather than retained as a separate theorem. Arbitrary signed coefficients, zero and singular inputs are included; no trace normalization is built into the map."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boseldui-ldui"),
                DeclarationHandle.Create(Prefix + "ldui"),
                H("Actual LDUI operator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("This is the existing normalized Dicke operator with diagonal weight P_ii and off-diagonal weight 2P_ij. It is an actual bipartite computational matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boseldui-cldui"),
                DeclarationHandle.Create(Prefix + "cldui"),
                H("Actual CLDUI companion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("The companion is the actual root partial transpose of the LDUI operator. Full Bose support belongs to the inverse-transposed witness, and is not asserted for the companion."))), DescribeRole.Definition))));
}
