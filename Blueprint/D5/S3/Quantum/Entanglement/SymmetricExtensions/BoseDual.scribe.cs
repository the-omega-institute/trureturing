using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseDualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The closed polar-sum identity for adapted DPS", H("The closed polar-sum identity for adapted DPS"),
        Blocks(
            Paragraph(Text("The real space is the existing HermitianMat space with its trace inner product. No unclosed dual-sum equality or unrestricted exact dual-certificate lifting is asserted. This is the closure-preserving application in the note by Haobo Ma and Wenlin Zhang.")),
            Describe.Lean(DescribeId.Create("bosedual-ordinarycone"),
                DeclarationHandle.Create(Prefix + "ordinaryCone"),
                H("ordinaryCone"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual ordinary DPS cone is represented as a closed convex cone in the real Hermitian space. Its defining lifts, cuts, and unnormalized marginals are unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosedual-bosesubspace"),
                DeclarationHandle.Create(Prefix + "boseSubspace"),
                H("boseSubspace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the full real linear space of Hermitian operators fixed by the actual pair-symmetric-projector sandwich. Positivity is supplied by DPS, not included in the subspace definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosedual-closed-dual-identity"),
                DeclarationHandle.Create(Prefix + "closed_dual_identity"),
                H("closed dual identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polar of the actual adapted DPS cone is the closure of the sum of the ordinary DPS polar and the orthogonal complement of the Bose support subspace. The proof applies finite-dimensional bipolarity to the closed conic sum and uses actual ordinary DPS closedness. The closure remains part of the conclusion."))),
                DescribeRole.Theorem))));
}
