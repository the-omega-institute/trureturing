using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ShiftOperators;

internal sealed class BackwardShiftCoisometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The backward shift is a norm-one coisometry with an isometric right inverse.",
        H("Backward Shift Coisometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("backward-shift-forward-translation-right-inverse"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry."
                    + "backward_shift_comp_forward_translation"),
                H("Forward translation is a right inverse"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Forall, Sp, F.Id("x"), InMacro, Sp,
                    Operatorname, Grp(F.Id("ZetaHilbertSpace")), Comma, Esc,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Open,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("u"), Close, Open, F.Id("x"), Close, Close,
                    Sp, Eq, Sp, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each prime-axis address u, applying the backward shift after the "
                    + "zero-extended forward translation returns every Hilbert vector x. "
                    + "At a translated coordinate, Function.extend evaluates to the original "
                    + "coefficient because normalizedTableAdd is injective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("backward-shift-surjective"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry."
                    + "backward_shift_surjective"),
                H("The backward shift is surjective"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("Surjective")), Open,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime-axis address u, backwardShiftCLM is onto. The explicit "
                    + "preimage of x is forwardTranslationCLM u x, so surjectivity follows "
                    + "directly from the right-inverse identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-translation-preserves-norm"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry."
                    + "forward_translation_norm_eq"),
                H("Forward translation is an isometry"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Forall, Sp, F.Id("x"), InMacro, Sp,
                    Operatorname, Grp(F.Id("ZetaHilbertSpace")), Comma, Esc,
                    Vert, Sp, Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("u"), Close, Open, F.Id("x"), Close, Vert,
                    Sp, Eq, Sp, Vert, Sp, F.Id("x"), Vert))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The forward translation is norm-nonincreasing by its zero-extension "
                    + "construction. Applying the norm-nonincreasing backward shift and then "
                    + "using the right-inverse identity gives the reverse inequality, hence "
                    + "exact preservation of the Hilbert norm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("backward-shift-operator-norm-one"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry."
                    + "backward_shift_operator_norm_eq_one"),
                H("The backward shift has norm one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Vert, Sp, Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Vert, Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen contraction estimate supplies the upper bound one. A unit "
                    + "single-support vector remains unit under forward translation and is "
                    + "sent back to itself, so the backward shift attains that bound and its "
                    + "operator norm is exactly one."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/BackwardShiftOperator")),
        ]));
}
