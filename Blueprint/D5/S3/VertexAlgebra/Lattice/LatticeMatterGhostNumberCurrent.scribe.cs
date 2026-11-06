using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeMatterGhostNumberCurrentDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticematterghostnumbercurrent-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCurrent." + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original ghost number current", H("The original ghost number current"), Blocks(
            Paragraph(Text("For every lattice datum D, use the original state space State D, original all-state field Y D and original tensorNumber D. There is no rank condition. The ghost state is minus ket {0,1}, in the existing bc vacuum convention, and its tensor lift has even parity.")),
            Node("numberCurrent", "The actual even current state",
                "For every D : LatticeData, numberCurrent D = LatticeAllStateField.vacuum D tensor (-ket {0,1}), with tensor product over Complex and the existing occupation basis on the ghost factor.", DescribeRole.Definition),
            Node("number_current_zero_mode", "The literal current zero mode",
                "For every D : LatticeData, the zero mode of Y D (numberCurrent D) equals tensorNumber D as an endomorphism of State D. The ghost normal product of ket {0} and ket {1} has state ket {0,1}. At mode zero it acts by the sum over i : Nat of b(-i-2)c(i+2), minus the sum of c(1-i)b(i-1). Splitting the original locally finite ghost-number normal sum at the exact integer cut 2 gives the negative of this action. The minus sign in numberCurrent therefore recovers the original ghostNumber, and the matter-vacuum mode supplier lifts it to tensorNumber. No endomorphism-valued infinite sum is taken.", DescribeRole.Theorem),
            Node("tensorNumber_stateField", "Covariance on all original integer modes",
                "For every D : LatticeData, every a,x : State D and every n : Int, tensorNumber D ((Y D a)[[n]] x) - (Y D a)[[n]] (tensorNumber D x) = (Y D (tensorNumber D a))[[n]] x. Apply the public original lattice iterate with first state numberCurrent D and iterate index zero. Its even component is the current itself and its odd component is zero. The binomial coefficient choose(0,i) kills every positive i, leaving exactly the commutator identity; neither a nor x needs a parity or ghost-number eigenvalue assumption.", DescribeRole.Theorem),
            Paragraph(Text("The new bridge is the identification of the literal even current with the existing number operator; the all-mode identity consumes it through the existing unrestricted iterate. It supplies number covariance for subsequent mode products and bracket constructions on this carrier. BRST cohomology, physical string theory and an AdS/CFT correspondence require further results; none is asserted here.")))));
}
