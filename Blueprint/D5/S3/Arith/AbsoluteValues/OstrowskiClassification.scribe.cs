using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues;

internal sealed class OstrowskiClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nontrivial real-valued absolute value on Q is real or uniquely p-adic.",
        H("Ostrowski Classification over the Rationals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-absolute-value-classification"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/AbsoluteValues/OstrowskiClassification.rational_absolute_value_classification"),
                H("Every nontrivial absolute value on Q is real or uniquely p-adic"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("f"), Sp, Colon, Sp,
                    F.Id("AbsoluteValue"), Open,
                    Mathbb, Grp(F.Id("Q")), Comma, Sp, Mathbb, Grp(F.Id("R")), Close, Comma, Sp,
                    F.Id("IsNontrivial"), Open, F.Id("f"), Close, Sp, Rightarrow, Sp,
                    F.Id("f"), Sp, Sim, Sp, F.Id("abs"), Underscore, Grp(Infty), Sp,
                    Lor, Sp, Exists, Bang, Sp, F.Id("p"), Sp, Colon, Sp,
                    F.Id("Prime"), Comma, Sp,
                    F.Id("f"), Sp, Sim, Sp, F.Id("abs"), Underscore, Grp(F.Id("p"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nontrivial real-valued absolute value f on the rationals, "
                        + "either f is equivalent to the standard real absolute value, or there "
                        + "is a unique natural prime p for which f is equivalent to the p-adic "
                        + "absolute value. Equivalence is the standard equivalence relation on "
                        + "absolute values used by Mathlib.")),
                    Paragraph(Text(
                        "The Lean theorem is a direct application of Mathlib's exact Ostrowski "
                        + "classification, Rat.AbsoluteValue.equiv_real_or_padic. The prime "
                        + "witness carries the Fact p.Prime instance required to construct the "
                        + "p-adic absolute value.")),
                    Paragraph(Text(
                        "This closes only the Ostrowski-classification clause of residual atom "
                        + "pzg-residual-3af9cb02d8cf0390d9bb00bf5e9962ee013252a6491d3f74d5ff2a3f8dcfe4ee "
                        + "at remark/27.34. It does not claim the atom's separate rational product "
                        + "formula or adelic compactness assertions."))),
                DescribeRole.Theorem
            )),
        []));
}
