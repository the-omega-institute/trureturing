using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class NativeOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual projector image and a spanning E-orbit intertwine the original quotient action.",
        H("The Original Native Orbit Intertwiner"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nativeorbit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/NativeOrbit.quotient_intertwiner"),
                H("The Original Native Orbit Intertwiner"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Pplus acts on the literal chosen NativeGround and equals the product over i of (I+F_i)/2, where F_i is the original normalized right action of the i-th binary unit. The nonzero-charge trace theorem from TwistedGround.OperatorAlgebra applies to these genuine original quotient elements. The projector has trace one, hence a nonzero actual image; its image seed then generates the character orbit.")),
                    Paragraph(Text("The basis indexed by all 4096 binary halves consists of E_x(Pplus(seed)). Both independence and spanning are established. Its coordinate isomorphism defines intertwiner from Ground(12) into the exact original chosen carrier.")),
                    Paragraph(Text("Translation acts by shifting the orbit labels, while the commuting F-subgroup acts diagonally by the distinct binary characters. These two identities give the full standard Weyl action. Restoring the original actionScalar gives an intertwiner of the actual quotient E/K representations, not an assumed equivalence or an identification of existential choices."))),
                DescribeRole.Theorem))));
}
