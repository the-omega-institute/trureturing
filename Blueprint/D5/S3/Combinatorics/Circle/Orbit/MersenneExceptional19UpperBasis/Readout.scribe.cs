using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis;

internal sealed class ReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer binary readout in arbitrary abelian groups — UNCOMPILED source preparation.",
        H("Integer binary readout in arbitrary abelian groups"),
        Blocks(
            Paragraph(Text("Finite words and a defined successor endpoint. For a group A and f:N->A, the shared read d f m is the sum of digit(m,i) acting by integer scalar multiplication on f(i), for 0<=i<d. This module works with the sealed additive-helper delta, retaining its original read and digit declarations. The theorem read_add_power explicitly requires j+1<d and 0<=m<m+2^j<2^d; j is a natural, so its nonnegativity is built into the type. No out-of-range successor is hidden in a total function.")),
            Paragraph(Text("Transport instead of division in a group. If f(i)=2^(i-j-1) f(j+1) for j<i<d, then read(m+2^j)-read(m)=(1-2 epsilon) f(j)+epsilon f(j+1), where epsilon=digit(m,j). The source proof inducts on j. At j=0, it splits off the low bit and uses the exact integer geometric word sum for the tail; the two Boolean alternatives are proved by Euclidean division. At j+1, adding the even power preserves parity and shifts the quotient by 2^j. Every quotient belongs to Z, and all actions on A are integer scalar actions, so the statement retains arbitrary torsion.")),
            Paragraph(Text("The actual high-row consumer. The additional word split and periodicity lemmas show that words differing by an integral multiple of 2^n have the same first n digits. Thus their d=n+3 readout difference is exactly the difference of their top three-bit readouts. HighRows applies this to the actual affine digits, while InternalRows and LowRows apply read_add_power to selected upper-to-upper changes. The generic helpers are consumed by these physical all-r proofs, rather than retained as separate certificates.")),
            Paragraph(Text("Evidence boundary. These are source proof scripts only. No elaboration, kernel check or axiom-closure receipt was produced, and the sealed additive dependencies also remain UNCOMPILED. The binary lemma is uniform; finite controls from the ordinary mathematical review are not premises of this source."))), []));
}
