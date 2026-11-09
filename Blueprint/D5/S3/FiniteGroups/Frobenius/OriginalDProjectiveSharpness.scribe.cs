using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class OriginalDProjectiveSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A modular dihedral representation separates conjugation freeness from a trivial subgroup action.",
        H("Original-D modular sharpness data"),
        Blocks(
            Paragraph(Text("This is the classical two-dimensional dihedral construction over the field F7. Let G be the dihedral group with 42 elements and N its cyclic rotation subgroup of order 21. Send one rotation to A = diag(2,4), and one reflection to the coordinate exchange S. The identities A cubed equals the identity, S squared equals the identity, and SAS equals the inverse of A define an action factoring through the dihedral group with six elements. For the convention sr(i) = s times r to the i, its matrix is S times A to the i; reversing this order changes the reflection matrices.")),
            Paragraph(Text("Every element outside N is a reflection, and conjugates each rotation to its inverse. A fixed rotation therefore has square equal to the identity. Since N has odd order 21, that rotation is the identity. This is precisely the original condition quantified over all g outside N and all n in N; it is not restricted to a chosen complement or to a chosen generator.")),
            Paragraph(Text("For irreducibility, let W be a nonzero invariant subspace and choose a nonzero vector (x,y) in W. Applying S when necessary makes x nonzero. Applying A minus four times the identity gives (5x,0). Division by 5x puts the first coordinate vector in W, and S puts the second coordinate vector in W. Hence W is the full space. The rotation restriction is nontrivial because A moves the first coordinate vector. This proof uses only the two distinct eigenvalues and the exchange of the coordinate axes; it does not use Maschke's theorem, an algebraic closure, or invertibility of the group order.")),
            Paragraph(Text("The tag-preserving projection from G to the dihedral group with six elements reduces rotation coordinates modulo three. Its kernel H consists of the seven rotations with coordinates divisible by three. The representation factors through this projection, so H acts trivially. H has order seven, while the Frobenius rotation subgroup N has order 21: these are different roles and different subgroups.")),
            Paragraph(Text("The mathematical distinction exposed here is between conjugation on N and the linear action on the representation space. Conjugation is fixed-point-free outside N, yet a subgroup of characteristic order acts trivially on an irreducible representation whose restriction to N is nontrivial. The order-seven subgroup supplies the concrete input for a separate projectivity obstruction over the group algebra. The combined data statement does not itself contain that homological conclusion. The example and its coordinate proof are classical, without a literature novelty claim.")))));
}
