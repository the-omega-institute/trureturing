using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCanonicalJointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCanonicalJoint.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniqueness of the actual joint reduced core.", H("Uniqueness of the actual joint reduced core"),
        Blocks(
            Paragraph(Text("The one-step diamond uses equality for overlapping choices in one frozen run, commutation with shifted indices for separated choices on one axis, and exact row-column commutation for orthogonal choices. The pinned Church-Rosser theorem joins arbitrary finite sequences. A rectangle with no adjacent frozen pair admits no further step, so both endpoints equal the common descendant.")),
Describe.Lean(DescribeId.Create("miuracanonicaljoint-0"),
                DeclarationHandle.Create(Prefix + "joint_reduced_core_unique"), H("Every deletion choice gives the same actual reduced rectangle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let h be any actual unit-edge integer height function. Suppose JointReduction h g and JointReduction h f are arbitrary legal sequences, and both g and f have no adjacent frozen pair along either physical axis. Then the dependent pairs consisting of the row dimension, the column dimension, and the complete integer function are equal. Thus both dimensions agree and the functions agree under the resulting dimension transport. No normalization or quotient is introduced; in particular this equality applies to the normalized residual arrays."))), DescribeRole.Theorem))));
}
