using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class ParallelogramNormLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inner-product geometry forces the squared-norm parallelogram identity.",
        H("Parallelogram Norm Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inner-product-norms-obey-the-parallelogram-law"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumContext/ParallelogramNormLaw."
                    + "inner_product_norm_parallelogram_law"),
                H("Inner-product norms obey the parallelogram law"),
                StatementSource.FromAuthor(ParallelogramFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any real inner-product space and vectors x and y, the sum of the "
                            + "squared lengths of x+y and x-y is twice the sum of their squared "
                            + "lengths. This is the parallelogram identity singled out by the "
                            + "Jordan-von Neumann criterion.")),
                    Paragraph(Text(
                        "Pinned Mathlib already proves the exact statement as "
                            + "parallelogram_law_with_norm. The Lean declaration is therefore "
                            + "the thinnest wrapper: it imports and applies that theorem directly.")),
                    Paragraph(Text(
                        "This closes only the parallelogram-law clause of appendix E.46. It does "
                            + "not formalize the triangle-group interpretation, Farey recursion, "
                            + "or the crossing-alignment problem stated elsewhere in that atom.")),
                    Paragraph(Text(
                        "Repository searches found no equivalent D5 declaration. Pinned-Mathlib "
                            + "source search found the exact theorem; the local smart-search name "
                            + "query returned no additional declaration."))),
                DescribeRole.Theorem))));

    private static Formula ParallelogramFormula()
    {
        Formula space = F.Id("E");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula Norm(Formula value) => Seq(Operatorname, Grp(F.Id("norm")), Open, value, Close);
        Formula SqNorm(Formula value) => Seq(Norm(value), Caret, Grp(D(2)));

        return Disp(Seq(
            Forall, Sp, space, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open, space, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("InnerProductSpace")), Open,
            Mathbb, Grp(F.Id("R")), Comma, Sp, space, Close, CloseBracket, Comma, Esc,
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, space, Comma, Esc,
            SqNorm(Grp(x, Sp, Plus, Sp, y)), Sp, Plus, Sp,
            SqNorm(Grp(x, Sp, Minus, Sp, y)), Sp, Eq, Sp, D(2),
            Open, SqNorm(x), Sp, Plus, Sp, SqNorm(y), Close, Dot));
    }
}
