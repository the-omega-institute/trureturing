using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class AdmissibleRelationSpaceGrowthDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/AdmissibleWords/AdmissibleRelationSpaceGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Full linear relations between admissible words have squared "
                + "Fibonacci dimension and golden-ratio-squared growth.",
            H("Relation-Space Growth for Admissible Words"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("admissible-relation-space-finrank"),
                    DeclarationHandle.Create(
                        Prefix + "admissible_relation_space_finrank"),
                    H("The relation-space dimension is a Fibonacci square"),
                    StatementSource.FromAuthor(DimensionFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Let H_n be the complex function space on the length-n "
                            + "Zeckendorf-admissible binary words. The existing "
                            + "admissible-word count gives dim H_n = F_(n+2), "
                            + "and the standard finrank formula for linear maps "
                            + "therefore gives dim End(H_n) = F_(n+2)^2."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("admissible-relation-space-growth"),
                    DeclarationHandle.Create(
                        Prefix + "admissible_relation_space_growth"),
                    H("Consecutive relation spaces grow by the golden ratio squared"),
                    StatementSource.FromAuthor(GrowthFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "After substituting the exact dimension formula, the "
                            + "consecutive ratio is the square of "
                            + "F_(n+3)/F_(n+2). Mathlib's Fibonacci ratio limit "
                            + "then yields the square of the golden ratio."))),
                    DescribeRole.Theorem))));

    private static Formula DimensionFormula() => Disp(Seq(
        Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Operatorname, Grp(F.Id("dim")), Underscore, F.Id("C"), Sp,
        Operatorname, Grp(F.Id("End")), Open, F.Id("H"), Underscore, F.Id("n"), Close,
        Sp, Eq, Sp,
        F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(2)), Caret, D(2), Dot));

    private static Formula GrowthFormula() => Disp(Seq(
        Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
        new Formula.Fraction(
            Grp(Operatorname, Grp(F.Id("dim")), Sp,
                Operatorname, Grp(F.Id("End")), Open,
                F.Id("H"), Underscore, Grp(F.Id("n"), Plus, D(1)), Close),
            Grp(Operatorname, Grp(F.Id("dim")), Sp,
                Operatorname, Grp(F.Id("End")), Open,
                F.Id("H"), Underscore, F.Id("n"), Close)),
        Sp, Eq, Sp, Varphi, Caret, D(2), Dot));
}
