using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class FiniteRecordPinchingIdempotenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite complete orthogonal projection family defines an idempotent unread-record map.",
        H("Finite Record Pinching Idempotence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-complete-record-pinching-is-idempotent"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Conditioning/FiniteRecordPinchingIdempotence."
                        + "finite_record_pinching_idempotent"),
                H("Finite complete record pinching is idempotent"),
                StatementSource.FromAuthor(IdempotenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be a finite family of complex matrix projections. Each P_k is "
                            + "self-adjoint and idempotent, distinct projections are pairwise "
                            + "orthogonal, and their sum is the identity.")),
                    Paragraph(Text(
                        "The unread-record map sends rho to the sum of the diagonal compressions "
                            + "P_k rho P_k. Applying it twice introduces two projection indices; "
                            + "orthogonality removes every cross term and projection idempotence "
                            + "retains each diagonal term, so the two functions are equal.")),
                    Paragraph(Text(
                        "The proof directly applies the frozen pointwise idempotence theorem and "
                            + "uses function extensionality only to expose the source claim as an "
                            + "equality of endomorphisms."))),
                DescribeRole.Theorem))));

    private static Formula IdempotenceFormula()
    {
        Formula n = F.Id("n"), labels = F.Id("K"), index = F.Id("k");
        Formula other = F.Id("l"), projection = Projection(index);
        Formula otherProjection = Projection(other), map = F.Id("E");

        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, labels, Comma, Sp,
            Call("Finite", n), Comma, Sp, Call("Finite", labels), Comma, RowBreak,
            F.Id("P"), Colon, Sp, labels, Sp, To, Sp, MatrixType(n), Comma, RowBreak,
            Open, Forall, Sp, index, InMacro, Sp, labels, Comma, Sp,
                projection, Caret, Grp(Star), Sp, Eq, Sp, projection,
                Sp, Land, Sp, projection, projection, Sp, Eq, Sp, projection, Close,
                Sp, Land, RowBreak,
            Open, Forall, Sp, index, Comma, Sp, other, InMacro, Sp, labels, Comma, Sp,
                index, Sp, Neq, Sp, other, Sp, Rightarrow, Sp,
                projection, otherProjection, Sp, Eq, Sp, D(0), Close,
                Sp, Land, RowBreak,
            Sum, Underscore, Grp(index, InMacro, Sp, labels), Sp,
                projection, Sp, Eq, Sp, F.Id("I"), Comma, RowBreak,
            map, Colon, Sp, MatrixType(n), Sp, To, Sp, MatrixType(n), Comma, Sp,
            map, Open, Rho, Close, Colon, Eq,
                Sum, Underscore, Grp(index, InMacro, Sp, labels), Sp,
                projection, Sp, Rho, Sp, projection, Comma, RowBreak,
            map, Sp, Circ, Sp, map, Sp, Eq, Sp, map, Dot));
    }

    private static Formula MatrixType(Formula n) => Seq(
        F.Id("M"), Underscore, Grp(n), Open, Mathbb, Grp(F.Id("C")), Close);

    private static Formula Projection(Formula index) => Seq(
        F.Id("P"), Underscore, Grp(index));
}
