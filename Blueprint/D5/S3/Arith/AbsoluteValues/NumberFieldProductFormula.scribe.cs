using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues;

internal sealed class NumberFieldProductFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized absolute values of a nonzero number-field element have product one.",
        H("The Product Formula for Number Fields"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("number-field-product-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/AbsoluteValues/NumberFieldProductFormula.number_field_product_formula"),
                H("The normalized absolute values over all places have product one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Sp, InMacro, Sp,
                    F.Id("K"), Caret, Grp(Times), Comma, Sp,
                    Prod, Underscore, F.Id("v"), Sp,
                    Lvert, Sp, F.Id("x"), Rvert, Underscore, F.Id("v"), Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonzero element x of a number field K, the product of all "
                        + "normalized absolute values of x is one. Membership in the "
                        + "multiplicative group of K is represented in Lean by a nonzero x : K.")),
                    Paragraph(Text(
                        "Pinned Mathlib decomposes all places into a finite product over infinite "
                        + "places, with each place raised to its real-or-complex multiplicity, and "
                        + "a finprod over finite places. The proof is the direct application "
                        + "NumberField.prod_abs_eq_one hx; no local reconstruction is introduced.")),
                    Paragraph(Text(
                        "The source also states the logarithmic sum-zero form as an equivalent "
                        + "presentation. This truth anchor formalizes the boxed multiplicative "
                        + "statement and adds no hypotheses or separate logarithmic declaration."))),
                DescribeRole.Theorem
            )),
        []));
}
