using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class FiniteDefectCharacterCarryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eight rank-three sign tables have the same character carry.",
        H("Finite defect character carry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-three-carry-is-wedge"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/FiniteDefectCharacterCarry.carry_is_wedge"),
                H("All alternating choices give one carry"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("g"), Comma, Sp,
                    F.Id("h"), InMacro, Sp, F.Id("E"), Comma, Esc,
                    Call("carry", Call("ell", F.Id("m")), F.Id("g"), F.Id("h")),
                    Eq, Call("wedge", F.Id("g"), F.Id("h"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The three coordinates of m choose an alternating "
                        + "bilinear correction to the explicit sign table f0. The value "
                        + "ell_m(g) is the sign on the three coordinate basis vectors, "
                        + "so it records the character of the second input. In the carry "
                        + "ell_m(g)+ell_m(h)-ell_m(g+h), every alternating correction "
                        + "cancels. The remaining three coordinates are the pairwise "
                        + "minors of g and h.")),
                    Paragraph(Text("Pairing this wedge with a third label gives the "
                        + "characteristic-two determinant. The identity concerns the "
                        + "finite sign system; it does not assert existence of a vertex "
                        + "operator algebra or its module category."))),
                DescribeRole.Theorem))));
}
