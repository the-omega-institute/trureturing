using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Jacobi;

internal sealed class CyclicFlagDiagramDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite cyclic flag graphs and their Jacobi quotient", H("Actual finite cyclic flag graphs and their Jacobi quotient"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-flag-carrier"),
                DeclarationHandle.Create(Prefix + "Diagram"), H("Finite flag graphs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A diagram has an arbitrary finite flag type, a fixed-point-free involutive edge pairing, and a vertex rotor whose cube is the identity. Exactly the fixed rotor flags are labeled leaves, each either ordinary red or blue or a true numbered anchor; all other rotor orbits have length three. No simplicity, connectedness, genus or edge-orientation hypothesis is imposed. Loops and parallel edges are retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-jacobi-quotient"),
                DeclarationHandle.Create(Prefix + "JacobiSpace"), H("The actual AS, IHX and ordinary CL relations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rational free module on these actual finite graphs is divided by the span of geometric relators: color- and rotor-preserving flag isomorphisms, reversal of one actual trivalent rotor with sign minus one, the literal six-flag I minus H plus X socket, and exchange of the colors on two actual consecutive ordinary legs. Numbered anchors never participate in CL, and flag isomorphisms preserve every anchor label. The socket preserves the entire edge pairing and every exterior flag, including arbitrary port-to-port pairings. The quotient is not defined by the kernel of a desired normalization map."))), DescribeRole.Definition))));
}
