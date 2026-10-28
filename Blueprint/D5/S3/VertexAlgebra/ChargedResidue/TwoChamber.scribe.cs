using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class TwoChamberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal collision residue coefficients.",
        H("TwoChamber"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-two-chamber-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/TwoChamber.two_chamber_coefficient"),
                H("The two signed chamber coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For all integer exponents a,b and coefficient index v, the signed difference between the coefficients at v and a+b-v of (1-X)^a*(1+X)^b equals the two local pole coefficients. Negative indices are extended by zero. Multiplication by 1-X and 1+X gives finite recurrences from a common negative exponent. The base case uses the quadratic coefficient change with its Jacobian, even and odd indices, and the interval where both input coefficients vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-signed-two-chamber-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/TwoChamber.signed_two_chamber_scalar"),
                H("The complete signed scalar collision comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("Specializing a=q+B and b=q-B identifies the two local coefficients with collisionScalar(v-2*q-2,B,-q-1-B) and its reflected B branch. Each branch keeps its own negative-degree test. The factors are 2^(-2*B)/2 and (-1)^v*2^(2*B)/2. The native outer-cutoff regrouping and reflected oscillator and ground-action identities connect this scalar formula to the arbitrary-input physical forward law. Each whole ordered range is enlarged before its monomial expansion."))),
                DescribeRole.Theorem))));
}
