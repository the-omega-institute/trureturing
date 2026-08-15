using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ShiftOperators;

internal sealed class BackwardShiftAdjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The backward shift and zero-extended translation are Hilbert adjoints whose star "
        + "products identify the orthogonal projection onto divisible coefficient families.",
        H("Backward Shift Adjoint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-backward-shift-adjoint-is-forward-translation"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint."
                    + "adjoint_backwardShiftCLM"),
                H("The backward-shift adjoint is forward translation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("adjoint")), Open,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bespoke source-pairing identity upgrades to the standard Hilbert-space "
                    + "adjoint: the adjoint of the backward shift is exactly the zero-extended "
                    + "forward translation. Taking adjoints again gives the reverse identity, "
                    + "so the two continuous linear maps are mutual adjoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-backward-shift-star-square-is-the-range-projection"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint."
                    + "adjoint_backward_shift_comp_self"),
                H("The backward-shift star square is the range projection"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("adjoint")), Open,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The product B-star B is exactly the divisibility filter. In the opposite "
                    + "order, B B-star is the identity, while the forward translation satisfies "
                    + "V-star V equal to the identity. Thus forward translation is a star "
                    + "isometry and the backward shift is a star coisometry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-range-projection-is-a-star-projection"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint."
                    + "shift_range_projection_isStarProjection"),
                H("The range projection is a star projection"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("IsStarProjection")), Open,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Adjoint reversal exchanges the two shift factors in the projection, so the "
                    + "divisibility filter is self-adjoint. Together with its established "
                    + "idempotence, this makes shiftRangeProjection a star projection rather "
                    + "than only a source-pairing-symmetric operator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-translation-ranges-over-divisible-families"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint."
                    + "range_forwardTranslationCLM"),
                H("Forward translation ranges over divisible families"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("range")), Open,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("u"), Close, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The submodule divisibleSubspace u consists of square-summable coefficient "
                    + "families supported only at addresses whose encodings are divisible by u. "
                    + "Zero-extension lands in this submodule, and every member is recovered by "
                    + "forward-translating its backward shift, so this submodule is exactly the "
                    + "range of forward translation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-divisibility-filter-is-the-orthogonal-projection"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint."
                    + "shift_range_projection_eq_starProjection"),
                H("The divisibility filter is the orthogonal projection"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("starProjection")), Open,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("u"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The star-projection characterization supplies the closed-range orthogonal "
                    + "projection instance for divisibleSubspace u. Since the filter range is "
                    + "that same submodule, uniqueness identifies shiftRangeProjection with the "
                    + "canonical starProjection onto divisible coefficient families."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-backward-shift-kernel-is-the-wandering-complement"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint."
                    + "ker_backwardShiftCLM"),
                H("The backward-shift kernel is the wandering complement"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Ker, Sp, Open,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("u"), Close, Caret, Grp(Perp)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The standard adjoint theorem identifies the kernel of a continuous linear "
                    + "map with the orthogonal complement of the range of its adjoint. Here that "
                    + "adjoint range is divisibleSubspace u, so the backward-shift kernel is "
                    + "precisely the wandering orthogonal complement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-wandering-complement-is-supported-off-multiples"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint."
                    + "mem_orthogonal_divisibleSubspace"),
                H("The wandering complement is supported off multiples"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Forall, Sp, F.Id("x"), InMacro, Sp,
                    Operatorname, Grp(F.Id("ZetaHilbertSpace")), Comma, Esc,
                    F.Id("x"), InMacro, Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("u"), Close, Caret, Grp(Perp), Sp,
                    Leftrightarrow, Sp, Forall, Sp, F.Id("b"), Comma, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("u"), Close, Sp, Mid, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("b"), Close, Sp, Rightarrow, Sp,
                    F.Id("x"), Open, F.Id("b"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Membership in the wandering complement has a coordinatewise description: "
                    + "the coefficient must vanish at every address divisible by u. The forward "
                    + "direction evaluates the zero backward shift at the exact quotient address; "
                    + "the converse checks every translated coordinate of the backward shift."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/BackwardShiftOperator")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/ShiftRangeProjection")),
        ]));
}
