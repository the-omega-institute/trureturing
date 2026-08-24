using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class RecordClassicalityFixedPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unread record fixed points are exactly the matrices with no cross-record blocks.",
        H("Record Classicality Fixed Point"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("record-classicality-is-unread-fixed-point"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Conditioning/RecordClassicalityFixedPoint."
                        + "record_classicality_fixed_point"),
                H("Record classicality is the unread fixed-point condition"),
                StatementSource.FromAuthor(FixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be a finite complete family of pairwise orthogonal, "
                            + "self-adjoint idempotent complex projections. The unread record "
                            + "map sums the diagonal compressions P_k rho P_k.")),
                    Paragraph(Text(
                        "The formal theorem directly applies the canonical unread-state "
                            + "fixed-point characterization. It retains both directions: a "
                            + "fixed matrix has every cross-record block equal to zero, and "
                            + "vanishing cross-record blocks reconstruct the fixed matrix by "
                            + "projection completeness."))),
                DescribeRole.Theorem))));

    private static Formula FixedPointFormula()
    {
        Formula n = F.Id("n"), labels = F.Id("K"), index = F.Id("k");
        Formula other = F.Id("l"), rho = F.Id("rho"), map = F.Id("U");
        Formula projection = Projection(index), otherProjection = Projection(other);

        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, labels, Comma, Sp,
            Call("Fintype", n), Comma, Sp, Call("Fintype", labels), Comma,
            RowBreak, Grp(),
            Forall, Sp, F.Id("P"), Colon, Sp, labels, Sp, To, Sp, MatrixType(n),
            Comma, Sp, rho, InMacro, Sp, MatrixType(n), Comma,
            RowBreak, Grp(),
            Call("Record", F.Id("P")), Sp, Rightarrow, Sp,
            map, Underscore, Grp(F.Id("P")), Open, rho, Close, Sp, Eq, Sp, rho,
            Sp, Leftrightarrow, Sp,
            Forall, Sp, index, Comma, Sp, other, InMacro, Sp, labels, Comma, Sp,
            index, Sp, Neq, Sp, other, Sp, Rightarrow, Sp,
            projection, Sp, rho, Sp, otherProjection, Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula MatrixType(Formula n) => Seq(
        F.Id("M"), Underscore, Grp(n), Open, Mathbb, Grp(F.Id("C")), Close);

    private static Formula Projection(Formula index) => Seq(
        F.Id("P"), Underscore, Grp(index));
}
