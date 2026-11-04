using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class CoherentUniformAmplificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform coherent rotation of a finite source space.",
        H("Whole-source coherent amplification"),
        Blocks(
            Paragraph(Text("Let S and L be arbitrary finite complex coordinate spaces, J an initialization isometry from S to L, C a supplied unitary on L, and P a self-adjoint idempotent good projection. Put U=CJ and suppose (PU)* PU=pI with 0<p<=1. For 0<p<1, Define W=PU/sqrt(p), B=(I-P)U/sqrt(1-p), theta=arcsin(sqrt(p)), and Q=(2UU*-I)(I-2P). The same Q acts on every source column; no unknown input state specifies a reflection.")),
            Describe.Lean(
                DescribeId.Create("uniform-operator-rotation"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/CoherentUniformAmplification.uniform_operator_rotation"),
                H("Every power rotates the entire source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/brassardhoyermoscatapp2002amplification")),
                Blocks(
                    Paragraph(Text("At p=1, U=W already. For 0<p<1, the operators W and B satisfy W*W=B*B=I and W*B=0. For every natural n, Q^n U=sin((2n+1)theta)W+cos((2n+1)theta)B. This is an equality of rectangular operators on the whole source, derived from the scalar success Gram. Induction proves the identity for all powers after the two reflections are evaluated on the two isometric ranges.")),
                    Paragraph(Text("For any reference index type and any reference matrix R, tensoring the same identity with R preserves it. In particular, R=I preserves every joint source-reference vector and its density matrix, including entangled inputs. The statement uses no input-dependent choice of plane.")),
                    Paragraph(Text("This result is the uniform rotation mechanism of standard amplitude amplification. Exact attenuation by an auxiliary coin, the integer iteration choice, deterministic circuit synthesis, and the O(p^(-1/2)) query bound are additional obligations. Coherent access to C and its inverse, both subspace reflections, and exact known coin rotations must be supplied; a destructive measurement interface does not supply them. Filter, reflection, and coin compilation costs are not included in a query count."))),
                DescribeRole.Theorem))));
}
