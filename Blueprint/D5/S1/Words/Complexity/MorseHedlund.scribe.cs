using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class MorseHedlundDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef MorseHedlund =
        LibraryNoteRef.Create("D5/L/Words/morsehedlund1940symbolic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Low factor complexity forces eventual periodicity for every one-sided word "
            + "over a finite alphabet.",
        H("The One-Sided Morse-Hedlund Theorem"),
        Blocks(
            Paragraph(Text(
                "Let x be a one-sided infinite word over an arbitrary finite alphabet. Factors "
                + "begin at natural indices. The conclusion permits a finite prefix before exact "
                + "repetition, matching the one-sided convention throughout the repository.")),
            Describe.Lean(
                DescribeId.Create("natural-start-word-factor-set"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MorseHedlund.wordFactorSet"),
                H("The factor set contains exactly the factors at natural starts"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("F"), Underscore, F.Id("x"), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    OpenBrace, Open, F.Id("x"), Open, F.Id("i"), Plus, F.Id("k"), Close,
                    Close, Underscore, Grp(F.Id("k"), InMacro, Sp, F.Id("Fin"), Open,
                    F.Id("n"), Close), Sp, Colon, Sp, F.Id("i"), InMacro, Mathbb,
                    Grp(F.Id("N")), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A length-n factor is represented by a function from Fin n to the alphabet. "
                    + "The finite ambient function type is filtered by occurrence at some natural "
                    + "starting index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-complexity-forces-eventual-periodicity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MorseHedlund."
                        + "eventuallyPeriodic_of_factor_complexity_le"),
                H("Low factor complexity forces eventual periodicity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Exists, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma,
                    Esc, Operatorname, Grp(F.Id("card")), Open, F.Id("F"), Underscore,
                    F.Id("x"), Open, F.Id("n"), Close, Close, Sp, Leq, Sp, F.Id("n"), Close,
                    Sp, Rightarrow, Sp, Exists, Sp, F.Id("s"), Comma, F.Id("p"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc, D(0), Sp, Lt, Sp, F.Id("p"),
                    Sp, Land,
                    Sp, Forall, Sp, F.Id("t"), InMacro, Mathbb, Grp(F.Id("N")), Comma,
                    Esc, F.Id("x"), Open, F.Id("s"), Plus, F.Id("t"), Plus,
                    F.Id("p"), Close, Eq, F.Id("x"), Open, F.Id("s"), Plus,
                    F.Id("t"), Close))),
                AssessedProvenance.FromLiterature(MorseHedlund),
                Blocks(
                    Paragraph(Text(
                        "Deleting the last letter maps length-(n+1) factors onto length-n "
                        + "factors, so complexity is monotone and begins at one. A bound at N "
                        + "therefore forces a flat step below N.")),
                    Paragraph(Text(
                        "At a flat step the deletion map is bijective, hence every occurring "
                        + "factor has a unique right extension. Two equal factors among one more "
                        + "natural starts than there are factors propagate forever and give a "
                        + "positive period on a tail.")),
                    Paragraph(Text(
                        "This is the one-sided finite-alphabet theorem only. It asserts neither "
                        + "recurrence nor balance, and it does not classify Sturmian words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("aperiodic-factor-complexity-floor"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MorseHedlund."
                        + "factor_complexity_ge_add_one_of_not_eventuallyPeriodic"),
                H("Every non-eventually-periodic word has the n plus one complexity floor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Open, Exists, Sp, F.Id("s"), Comma, F.Id("p"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc, D(0), Sp, Lt, Sp, F.Id("p"), Sp,
                    Land, Sp, Forall, Sp, F.Id("t"), InMacro, Mathbb, Grp(F.Id("N")),
                    Comma, Esc, F.Id("x"), Open, F.Id("s"), Plus, F.Id("t"), Plus,
                    F.Id("p"), Close, Eq, F.Id("x"), Open, F.Id("s"), Plus,
                    F.Id("t"), Close, Close, Sp, Rightarrow, Sp, Forall, Sp,
                    F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("n"), Plus, D(1), Sp, Leq, Sp, Operatorname, Grp(F.Id("card")),
                    Open, F.Id("F"), Underscore, F.Id("x"), Open, F.Id("n"),
                    Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the direct contrapositive of the one-sided Morse-Hedlund theorem. "
                    + "The inequality is stated as n plus one less than or equal to the factor "
                    + "count, avoiding a hidden conversion between strict and non-strict "
                    + "bounds."))),
                DescribeRole.Theorem)),
        []));
}
