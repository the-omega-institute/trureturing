using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FockSpace;

internal sealed class ForbiddenNeighbourTraceExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/FockSpace/ForbiddenNeighbourTraceExtension.";
    private static Formula Dd => F.Id("d");
    private static Formula J => F.Id("j");
    private static Formula W => F.Id("w");
    private static Formula U => F.Id("u");
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula L(Formula w) => Sub(F.Id("L"), w);
    private static Formula C(Formula w) => Sub(F.Id("C"), w);
    private static Formula Tr(Formula a) => Seq(Operatorname, Grp(F.Id("Tr")), Open, a, Close);
    private static Formula Total(Formula w, Formula last) => Seq(Sum,
        Underscore, Grp(J, Eq, D(0)), Caret, Grp(last), Sub(w, J));
    private static Formula OldLast => Seq(D(2), Dd, Minus, D(2));
    private static Formula Degree => Seq(Forall, Sp, Dd, InMacro, Sp, Mathbb, Grp(F.Id("N")),
        Comma, Dd, Ge, Sp, D(1), Colon);
    private static Formula RealVector(Formula w, Formula length) => Seq(w, InMacro, Sp,
        Pow(Seq(Mathbb, Grp(F.Id("R"))), length));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative bidiagonal weights have fixed trace and zero-tail extension rigidity.",
        H("Forbidden-Neighbour Trace and Extension"),
        Blocks(
            Paragraph(Text("L_w is the actual square-root lower-bidiagonal matrix: its diagonal "
                + "entry i is sqrt(w(2i)), and its entry below that diagonal is sqrt(w(2i+1)). "
                + "C_w is the actual forbidden-neighbour configuration polynomial. Indices below "
                + "start at zero. All real weights may vanish or repeat.")),
            Describe.Lean(DescribeId.Create("lower-bidiagonal-trace-weights"),
                DeclarationHandle.Create(Prefix + "lower_bidiagonal_trace_weights"),
                H("The trace counts every weight"),
                StatementSource.FromAuthor(Disp(Seq(Degree,
                    RealVector(W, Seq(D(2), Dd, Minus, D(1))), Comma,
                    Open, Forall, Sp, J, Colon, Sub(W, J), Ge, Sp, D(0), Close, Implies, Sp,
                    Tr(Seq(L(W), Pow(L(W), F.Id("T")))), Eq, Total(W, OldLast), Land, Sp,
                    Tr(Seq(Pow(L(W), F.Id("T")), L(W))), Eq, Total(W, OldLast)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace of L_w L_w^T is the sum of its squared entries. "
                    + "Splitting diagonal and subdiagonal entries enumerates the even and odd "
                    + "weight indices exactly once. Nonnegativity justifies sqrt(w)^2=w. "
                    + "Cyclicity gives the same trace for L_w^T L_w."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unchanged-weights-zero-append"),
                DeclarationHandle.Create(Prefix + "unchanged_weights_zero_append"),
                H("Two appended weights vanish"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Degree, RealVector(W, Seq(D(2), Dd, Minus, D(1))), Comma,
                        RealVector(U, Seq(D(2), Dd, Plus, D(1)))),
                    Seq(Open, Forall, Sp, J, Colon, Sub(U, J), Ge, Sp, D(0), Close, Land, Sp,
                        Open, Forall, Sp, D(0), Le, Sp, J, Le, Sp, OldLast, Colon,
                        Sub(U, J), Eq, Sub(W, J), Close, Land, Sp,
                        Total(U, Seq(D(2), Dd)), Eq, Total(W, OldLast), Implies),
                    Seq(Sub(U, Seq(D(2), Dd, Minus, D(1))), Eq, D(0), Land, Sp,
                        Sub(U, Seq(D(2), Dd)), Eq, D(0), Land, Sp,
                        L(U), Eq, Operatorname, Grp(F.Id("diag")), Open, L(W), Comma, D(0), Close, Land, Sp,
                        C(U), Eq, C(W))
                ]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum splits into the unchanged prefix and its last two "
                    + "nonnegative entries, so both last entries are zero. The displayed direct "
                    + "sum means reindexing L_u by finSumFinEquiv from Fin d plus Fin 1: the old "
                    + "block is L_w and every new entry is zero. The public endpoint recurrence "
                    + "applied twice then gives C_u=C_w. This includes d=1. No unchanged-block "
                    + "claim is made for L_u^T L_u before the appended weights vanish."))), DescribeRole.Theorem))));
}
