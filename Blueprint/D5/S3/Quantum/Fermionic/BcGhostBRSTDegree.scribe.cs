using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostBRSTDegreeDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("bcghostbrstdegree-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostBRSTDegree." + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ghost degree of the original cubic charge", H("Ghost degree of the original cubic charge"), Blocks(
            Paragraph(Text("The number operator is the original locally finite bc ghost-number operator. The cubic is normally ordered with the original b and c vacuum cuts; no intercept is added.")),
            Node("ghost_number_Qg", "The cubic has ghost degree one", "On the original complex countable occupation Fock space, ghostNumber * Qg - Qg * ghostNumber = Qg. Each normally ordered cubic has two c factors of degree one and one b factor of degree minus one. The commutator passes through the statewise finite cubic sums, using finite support at both v and ghostNumber v.", DescribeRole.Theorem),
            Paragraph(Text("This algebraic result is a step toward the Monster, VOA/CFT, anomaly and fusion programme. BRST cohomology, the no-ghost theorem, a physical string model and an AdS/CFT correspondence require further constructions.")))));
}
