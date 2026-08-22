using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class UnreadStateOrthogonalProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unread measurement projects orthogonally onto block-diagonal matrices.",
        H("Unread-State Orthogonal Projection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unread-record-measurement-is-the-block-diagonal-orthogonal-projection"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Conditioning/UnreadStateOrthogonalProjection."
                        + "unread_state_orthogonal_projection"),
                H("Unread measurement is the block-diagonal orthogonal projection"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be a finite complete family of pairwise orthogonal "
                            + "self-adjoint idempotent complex matrix projections. The unread "
                            + "measurement channel is constructed as the sum of the compressed "
                            + "blocks P_i X P_i; it is not defined from the target range.")),
                    Paragraph(Text(
                        "The channel is idempotent and self-adjoint for the trace pairing. Its "
                            + "range is exactly the matrices whose P_i X P_j cross blocks vanish "
                            + "when i and j differ.")),
                    Paragraph(Text(
                        "Every matrix splits into its unread image and discarded residual. These "
                            + "two named components are Hilbert--Schmidt orthogonal, and the "
                            + "existing trace definition of squared Hilbert--Schmidt norm gives "
                            + "the displayed Pythagorean identity."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Rangle, Underscore, Grp(F.Id("HS")));

    private static Formula NormSquare(Formula value) =>
        Seq(new Formula.Norm(value), Underscore, Grp(F.Id("HS")), Caret, Grp(D(2)));

    private static Formula TheoremFormula()
    {
        Formula indexType = Kappa;
        Formula matrixIndex = F.Id("n");
        Formula family = F.Id("P");
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula projectorI = Subscript(family, i);
        Formula projectorJ = Subscript(family, j);
        Formula matrixSpace = Seq(Subscript(F.Id("M"), matrixIndex),
            Open, Mathbb, Grp(F.Id("C")), Close);
        Formula channel = Subscript(Seq(Mathcal, Grp(F.Id("D"))), family);
        Formula channelX = Apply(channel, x);
        Formula channelY = Apply(channel, y);
        Formula residual = Seq(x, Sp, Minus, Sp, channelX);
        Formula blockSpace = Subscript(Seq(Mathcal, Grp(F.Id("B"))), family);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, matrixIndex, Comma, Sp, indexType, Comma, Sp, family, Colon, Sp,
            indexType, Sp, To, Sp, matrixSpace, Comma, Sp,
            Call("Finite", matrixIndex), Comma, Sp, Call("Finite", indexType), Comma,
            RowBreak, Grp(),
            Call("CompleteOrthogonalProjectionFamily", family), Comma, Sp,
            Open, Forall, Sp, x, InMacro, Sp, matrixSpace, Comma, Sp,
            channelX, Sp, Eq, Sp, Sum, Underscore, Grp(i), Sp,
            projectorI, Sp, x, Sp, projectorI, Close, Comma, RowBreak, Grp(),
            blockSpace, Sp, Eq, Sp, OpenBrace, x, Sp, Mid, Sp, Forall, Sp, i, Comma, Sp, j,
            Comma, Sp, i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            projectorI, Sp, x, Sp, projectorJ, Sp, Eq, Sp, D(0), CloseBrace, Comma,
            RowBreak, Grp(),
            Rightarrow, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp,
            Apply(channel, channelX), Sp, Eq, Sp, channelX, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            Inner(channelX, y), Sp, Eq, Sp, Inner(x, channelY), Close,
            Sp, Land, RowBreak, Grp(),
            Call("range", channel), Sp, Eq, Sp, blockSpace, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp,
            x, Sp, Eq, Sp, channelX, Sp, Plus, Sp, Open, residual, Close, Sp, Land, Sp,
            Inner(channelX, residual), Sp, Eq, Sp, D(0), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp,
            NormSquare(x), Sp, Eq, Sp, NormSquare(channelX), Sp, Plus, Sp,
            NormSquare(residual), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
