using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.NicaCovariance;

internal sealed class DoubleCommutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprime address translations doubly commute and their divisible subspaces meet at "
        + "the product address.",
        H("Coprime Double Commutation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coprime-backward-and-forward-shifts-commute"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/DoubleCommutation."
                    + "backward_shift_comp_forward_translation_of_coprime"),
                H("Coprime backward and forward shifts commute"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("Coprime")), Open,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("u"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("v"), Close, Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("v"), Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a coordinate divisible by v, both compositions recover the same "
                    + "coefficient after swapping the normalized additions of u and v. At every "
                    + "other coordinate, coprimality cancels the u factor from the divisibility "
                    + "test, so both zero-extended translations vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coprime-forward-translations-doubly-commute"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/DoubleCommutation."
                    + "adjoint_forward_translation_comp_of_coprime"),
                H("Coprime forward translations doubly commute"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("Coprime")), Open,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("u"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("v"), Close, Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("adjoint")), Open,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("u"), Close, Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("v"), Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("adjoint")), Open,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("u"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The adjoint of forward translation by u is the backward shift by u. The "
                    + "double-commutation identity is therefore the preceding coprime commutation "
                    + "theorem after rewriting that adjoint, with no additional coordinate "
                    + "argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coprime-divisible-subspaces-meet-at-the-product-address"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/DoubleCommutation."
                    + "divisibleSubspace_inf_of_coprime"),
                H("Coprime divisible subspaces meet at the product address"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("Coprime")), Open,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("u"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("v"), Close, Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("u"), Close, Sp,
                    Operatorname, Grp(F.Id("inf")), Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")), Open,
                    Operatorname, Grp(F.Id("normalizedTableAdd")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Membership in the meet means that a coefficient family vanishes away from "
                    + "both divisibility supports. For coprime encoded addresses, divisibility by "
                    + "their product is equivalent to simultaneous divisibility by u and v, so "
                    + "the meet is exactly the subspace at their normalized table sum."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/NicaCovariance/SemigroupRelations")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/ShiftRangeProjection")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/BackwardShiftOperator")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry")),
        ]));
}
