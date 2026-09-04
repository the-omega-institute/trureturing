using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ShiftOperators;

internal sealed class InverseBlaschkeHistoryDeletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The adjoint of an inner isometry is a coisometry that deletes exactly its finite "
        + "model-space histories, with index equal to their dimension.",
        H("Inverse Blaschke History Deletion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inverse-blaschke-history-deletion"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/InverseBlaschkeHistoryDeletion."
                    + "inverse_blaschke_history_deletion"),
                H("Inverse inner factors delete the model-space history"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be an isometry on a complete real or complex Hilbert space. "
                        + "Set T equal to its adjoint, let K be the orthogonal complement of "
                        + "the range of V, and suppose K has finite dimension m. Then T is a "
                        + "coisometry, its initial projection is the identity minus the "
                        + "orthogonal projection onto K, and its kernel is exactly K.")),
                    Paragraph(Text(
                        "The defect I minus VV-star is proved to be a star projection whose "
                        + "range is K. Surjectivity follows from T composed with V being the "
                        + "identity. Consequently T is Fredholm with index m, while Mathlib's "
                        + "quotientEquivOrthogonal explicitly identifies the cokernel of V with "
                        + "the same model space K.")),
                    Paragraph(Text(
                        "The source statement referred directly to finite Blaschke products, "
                        + "Hardy-space Toeplitz operators, and their model spaces, for which the "
                        + "repository has no construction. The formal theorem therefore states "
                        + "the exact operator data supplied by that analytic setting: isometry "
                        + "of V and finite model-space dimension. No Toeplitz or Blaschke result "
                        + "is assumed under an opaque name."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula hilbert = F.Id("H");
        Formula forward = F.Id("V");
        Formula inverse = F.Id("T");
        Formula model = F.Id("K");
        Formula projection = F.Id("P_K");
        Formula adjointForward = Seq(forward, Caret, Grp(Star));
        Formula adjointInverse = Seq(inverse, Caret, Grp(Star));
        Formula rangeForward = Call("ran", forward);

        return Disp(Seq(
            inverse, Sp, Colon, Eq, Sp, adjointForward, Comma, Quad,
            model, Sp, Colon, Eq, Sp, Open, rangeForward, Close, Caret, Grp(Perp), Comma, Quad,
            projection, Sp, Colon, Eq, Sp, F.Id("I"), Sp, Minus, Sp,
            forward, Sp, adjointForward, Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("Isometry")), Open, forward, Close, Sp, Land, Sp,
            Operatorname, Grp(F.Id("dim")), Open, model, Close, Sp, Eq, Sp, F.Id("m"), Sp,
            Longrightarrow, Sp, inverse, Sp, adjointInverse, Sp, Eq, Sp, F.Id("I"), Sp, Land, Sp,
            adjointInverse, Sp, inverse, Sp, Eq, Sp, F.Id("I"), Sp, Minus, Sp, projection,
            Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("ran")), Open, projection, Close, Sp, Eq, Sp,
            Ker, Open, inverse, Close, Sp, Eq, Sp, model, Sp, Land, Sp,
            Operatorname, Grp(F.Id("Surjective")), Open, inverse, Close, Sp, Land, Sp,
            Operatorname, Grp(F.Id("Fredholm")), Open, inverse, Close, Sp, Land, Sp,
            Operatorname, Grp(F.Id("ind")), Open, inverse, Close, Sp, Eq, Sp, F.Id("m"),
            Comma, RowBreak, Grp(),
            hilbert, Sp, Slash, Sp, rangeForward, Sp, Equiv, Sp, model, Dot));
    }
}
