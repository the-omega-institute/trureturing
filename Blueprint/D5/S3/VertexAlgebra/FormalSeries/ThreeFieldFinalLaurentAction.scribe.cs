using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldFinalLaurentActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentAction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual six-factor Laurent action", H("The actual six-factor Laurent action"), Blocks(
            Describe.Lean(DescribeId.Create("raw-r-action-transport"),
                DeclarationHandle.Create(Prefix + "raw_R_action_transport"),
                H("raw_R_action_transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every commutative complex algebra R, every generally infinite three-variable formal series P, all natural k and a, and every signed exponent e, the finite polynomialAction of x^k y^k (x+y)^k (x+y+z)^a0 (y+z)^a1 z^a2 on laurentCoefficient P k a equals signedExtend P e. Monomial actions become multiplication by XYZ,YZ,Z in the native chart. Finite addition, multiplication and powers transport the literal six factors. Removing their native monomial shift leaves W(e)=(e0,e0+e1,e0+e1+e2); a negative W coordinate vanishes, and a negative raw coordinate with nonnegative W gives an unsorted native index. Zero exponents and the zero algebra remain included. This algebraic statement supplies no channel identification, convergence, sewing or vertex-algebra completion."))), DescribeRole.Theorem))));
}
