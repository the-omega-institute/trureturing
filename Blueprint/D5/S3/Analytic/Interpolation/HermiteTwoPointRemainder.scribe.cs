using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class HermiteTwoPointRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-point Hermite interpolation has a cubic remainder, and a positive third derivative fixes its sign.",
        H("Two-point Hermite remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hermite-two-point-remainder"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/HermiteTwoPointRemainder.hermite_two_point_remainder"),
                H("Cubic remainder and strict sign"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("f"), Sp, Minus, Sp, F.Id("p"), Sp, Eq, Sp,
                    Frac, Grp(Call("iteratedDeriv", Num(3), F.Id("f"))), Grp(Num(6)),
                    Sp, Times, Sp, Grp(F.Id("x"), Minus, F.Id("L"), Close),
                    Caret, Grp(Num(2)), Sp, Times, Sp, Grp(F.Id("x"), Minus, F.Id("H"), Close),
                    Sp, Comma, Sp, F.Id("f"), Sp, Minus, Sp, F.Id("p"), Sp, Lt, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an interior point between two ordered nodes, a function and its Hermite interpolant agree through first order at the left node and agree in value at the right node. Repeated applications of Rolle's theorem produce an interior point where the third derivative determines the remainder. The cubic factor has a squared left factor and a negative right factor, so a positive third derivative gives a strict negative remainder."))),
                DescribeRole.Theorem))));
}
