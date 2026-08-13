using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class FrameBundleDimensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A local frame-coordinate space over n coordinates has dimension n+n^2.",
        H("Frame Bundle Dimension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-frame-coordinates-have-dimension-n-plus-n-squared"),
                DeclarationHandle.Create(
                    "D5/S0/Tower/FrameBundleDimension.frame_coordinate_finrank"),
                H("Local frame coordinates have dimension n plus n squared"),
                StatementSource.FromAuthor(Disp(Equal(
                    Call("finrank", F.Id("K"), Call("FrameCoordinateSpace", F.Id("K"), F.Id("n"))),
                    Add(F.Id("n"), Multiply(F.Id("n"), F.Id("n")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Over a field K, a local coordinate description consists of a vector "
                        + "with n coefficients and a frame matrix with n by n coefficients. "
                        + "Their product space therefore has the displayed finite dimension.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. Module.finrank_prod gives "
                        + "the dimension of the product, while Module.finrank_pi_fintype and "
                        + "Module.finrank_fintype_fun_eq_card compute the two function-space "
                        + "dimensions. The Lean proof is a thin normalization wrapper over these "
                        + "library declarations; no packaged theorem for this combined model was found.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the leading dimension clause only. "
                        + "The canonical fixed-section assertion, the information interpretation, "
                        + "and the later identifications remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
