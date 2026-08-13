using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class IrrationalContinuedFractionNonterminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "An irrational real has a nonterminating continued-fraction computation.",
            H("Irrational Continued-Fraction Nontermination"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("irrational-continued-fraction-nontermination"),
                    DeclarationHandle.Create(
                        "D5/S1/Depth/IrrationalContinuedFractionNontermination.irrational_continued_fraction_nontermination"),
                    H("Irrational inputs do not terminate"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, F.Id("x"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                        Operatorname, Grp(F.Id("Irrational")), Open, F.Id("x"), Close,
                        Sp, Rightarrow, Sp, Neg, Operatorname, Grp(F.Id("Terminates")), Open,
                        Operatorname, Grp(F.Id("continuedFraction")), Open, F.Id("x"), Close, Close,
                        Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The declaration closes only the source clause that every irrational "
                            + "continued-fraction computation is infinite. It does not claim the "
                            + "separate error monotonicity, golden extremality, or comparison clauses.")),
                        Paragraph(Text(
                            "Mathlib provides GenContFract.terminates_iff_rat, which identifies "
                            + "termination exactly with being a rational real. The proof applies "
                            + "that equivalence and contradicts Irrational directly, so no new "
                            + "continued-fraction machinery is introduced."))),
                    DescribeRole.Theorem))));
}
