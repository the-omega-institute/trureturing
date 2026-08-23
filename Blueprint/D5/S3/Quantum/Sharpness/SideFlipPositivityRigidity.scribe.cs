using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Sharpness;

internal sealed class SideFlipPositivityRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A side-flip-invariant nonnegative complex subspace is isotropic for the reflection form.",
        H("Side-Flip Positivity Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("side-flip-invariant-nonnegative-subspace-is-isotropic"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Sharpness/SideFlipPositivityRigidity."
                    + "side_flip_positive_rigidity"),
                H("A side-flip-invariant nonnegative subspace is isotropic"),
                StatementSource.FromAuthor(RigidityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the two complex evaluation coordinates, the side operator fixes the "
                            + "first coordinate and negates the second, while reflection exchanges "
                            + "the two coordinates. The associated real Hermitian quadratic form "
                            + "therefore changes sign under the side operator.")),
                    Paragraph(Text(
                        "Let W be a complex linear subspace preserved by the side operator. If the "
                            + "reflection form is nonnegative on every vector in W, then applying "
                            + "nonnegativity both to v and to its side flip bounds the form by zero "
                            + "from both directions. Thus the form vanishes throughout W.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no exact theorem for this "
                            + "coordinate side-flip rigidity statement. The coordinate operators "
                            + "and reflection form are constructed directly, and the proof uses "
                            + "the explicit sign-flip computation."))),
                DescribeRole.Theorem))));

    private static Formula RigidityFormula()
    {
        Formula space = F.Id("W");
        Formula vector = F.Id("v");
        Formula side = Seq(F.Id("Z"), Underscore, Rho);
        Formula form = Seq(F.Id("q"), Underscore, F.Id("J"));
        Formula complexPlane = Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(D(2)));

        return Disp(Seq(
            space, Sp, Subseteq, Sp, complexPlane, Comma, Esc,
            side, Open, space, Close, Sp, Subseteq, Sp, space, Comma, Esc,
            Open, Forall, Sp, vector, Sp, InMacro, Sp, space, Comma, Esc,
            form, Open, vector, Close, Sp, Ge, Sp, D(0), Close,
            Sp, Rightarrow, Sp,
            Forall, Sp, vector, Sp, InMacro, Sp, space, Comma, Esc,
            form, Open, vector, Close, Sp, Eq, Sp, D(0), Dot));
    }
}
