using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseLDUIDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Dicke and LDUI coordinates", H("Exact Dicke and LDUI coordinates"), Blocks(
            Paragraph(Text("The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.")),
            Paragraph(Text("For an arbitrary upper-triangular real Y, the diagonal coordinate is P_ii=Y_ii and each off-diagonal coordinate is P_ij=Y_min(i,j),max(i,j)/2. Substitution into the actual LDUI operator uses the off-diagonal weight 2P_ij, so the exact half factor cancels. Signed, zero and singular inputs remain in scope and no trace normalization is imposed.")),
            Describe.Lean(DescribeId.Create("boseldui-ldui"),
                DeclarationHandle.Create(Prefix + "ldui"),
                H("Actual LDUI operator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("This is the existing normalized Dicke operator with diagonal weight P_ii and off-diagonal weight 2P_ij. It is an actual bipartite computational matrix."))), DescribeRole.Definition),
            Paragraph(Text("The CLDUI companion is the actual product-basis root transpose of the LDUI matrix. The companion need not have full Bose support; that support belongs to the inverse-transposed witness. The root transpose and the Y/P half-factor application are retained here as complete exposition.")))));
}
