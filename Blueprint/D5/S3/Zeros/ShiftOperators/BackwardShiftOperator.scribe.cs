using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ShiftOperators;

internal sealed class BackwardShiftOperatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen coefficient pullback is a contraction adjoint with divisibility-truncated basis action.",
        H("Backward Shift Operator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("backward-shift-operator-norm-at-most-one"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftOperator."
                    + "backward_shift_operator_norm_le_one"),
                H("The backward shift is a contraction"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Vert, Sp, Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Vert, Sp, Le, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime-axis address u, backwardShiftCLM is the frozen "
                    + "backwardShift coefficient pullback bundled as a continuous linear map "
                    + "on ZetaHilbertSpace. Its operator norm is at most one because right "
                    + "multiplication of encoded addresses is injective, so the pulled-back "
                    + "square-norm sum is bounded by the original sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("backward-shift-is-source-pairing-adjoint"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftOperator."
                    + "backward_shift_sourcePairing_adjoint"),
                H("The backward shift is the translation adjoint"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), InMacro, Sp,
                    Operatorname, Grp(F.Id("ZetaHilbertSpace")), Comma, Esc,
                    Operatorname, Grp(F.Id("sourcePairing")), Open,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Open, F.Id("x"), Close,
                    Comma, Sp, F.Id("y"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("sourcePairing")), Open, F.Id("x"), Comma, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("u"), Close, Open, F.Id("y"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all Hilbert vectors x and y, the source pairing of the backward "
                    + "shift of x with y equals the source pairing of x with the forward "
                    + "translation of y. No forward shift was frozen in the repository, so "
                    + "forwardTranslationCLM is constructed here independently by extending "
                    + "coefficients by zero off the injective multiplicative-translation image. "
                    + "The identity follows by reindexing that zero extension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("backward-shift-basis-subtraction-with-truncation"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftOperator."
                    + "backward_shift_basis_subtraction"),
                H("Basis kets subtract exactly on divisible addresses"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("b"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Open,
                    Operatorname, Grp(F.Id("ket")), Open, F.Id("b"), Close, Close,
                    Sp, Eq, Sp, Begin, Grp(F.Id("cases")),
                    Operatorname, Grp(F.Id("ket")), Open,
                    Operatorname, Grp(F.Id("normalizedTableSub")),
                    Open, F.Id("b"), Comma, Sp, F.Id("u"), Close, Close,
                    Comma, Amp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")), Open, F.Id("u"), Close,
                    Sp, Mid, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")), Open, F.Id("b"), Close,
                    RowBreak,
                    D(0), Comma, Amp, Neg, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")), Open, F.Id("u"), Close,
                    Sp, Mid, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")), Open, F.Id("b"), Close,
                    End, Grp(F.Id("cases"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here ket(b) denotes the normalized single-support vector lp.single 2 b 1. "
                    + "If the positive-natural encoding of u divides that of b, the backward "
                    + "shift sends ket(b) to ket(normalizedTableSub b u); if not, it sends the "
                    + "ket to zero. The subtraction is PNat.divExact transported through the "
                    + "frozen primeAxisEncoding, and normalizedTableSub_add_cancel proves the "
                    + "divisible branch rather than installing it by definition."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/SpectralShift")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/SpectralHilbert")),
        ]));
}
