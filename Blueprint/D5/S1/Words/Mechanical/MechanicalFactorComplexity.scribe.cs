using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalFactorComplexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Count factors of every irrational lower mechanical word at an arbitrary intercept.",
        H("Factor Complexity of Irrational Lower Mechanical Words"),
        Blocks(
            Paragraph(Text(
                "Fix an irrational real slope alpha in the half-open interval from zero to one "
                + "and an arbitrary real intercept rho. Factors begin only at natural indices, "
                + "and the lower mechanical word retains its frozen half-open boundary convention.")),
            Describe.Lean(
                DescribeId.Create("lower-mechanical-factor-set"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalFactorComplexity.lowerMechanicalFactorSet"),
                H("The factor set records exactly the factors at natural starts"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("FactorSet"), Open, Alpha, Comma, Rho, Comma, F.Id("n"), Close,
                    Sp, Eq, Sp, OpenBrace,
                    F.Id("w"), Underscore, Alpha, Comma, Rho,
                    Open, F.Id("i"), Comma, F.Id("n"), Close,
                    Sp, Colon, Sp, F.Id("i"), InMacro, Mathbb, Grp(F.Id("N")), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A finite Boolean function represents each candidate word. Filtering by "
                    + "occurrence and mapping through List.ofFn gives a finite set whose membership "
                    + "is equivalent to occurrence at some natural starting index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("irrational-lower-mechanical-factor-complexity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalFactorComplexity.lower_mechanical_factor_complexity"),
                H("Every irrational lower mechanical word has complexity n plus one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Alpha, Comma, Rho, InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    D(0), Sp, Leq, Sp, Alpha, Sp, Lt, Sp, D(1), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close,
                    Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("card")), Open,
                    F.Id("FactorSet"), Open, Alpha, Comma, Rho, Comma, F.Id("n"), Close,
                    Close, Sp, Eq, Sp, F.Id("n"), Sp, Plus, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The upper bound classifies a factor by how many of its n irrational "
                        + "breakpoints lie at or below the translated phase. Equal ranks give equal "
                        + "successive prefix counts and hence equal letters.")),
                    Paragraph(Text(
                        "For the lower bound, irrational rotation is dense after translation by "
                        + "rho. Every open interval between adjacent sorted breakpoints therefore "
                        + "contains a natural-start phase, realizing every rank from zero through n.")),
                    Paragraph(Text(
                        "The theorem is a factor-complexity statement for lower mechanical words. "
                        + "It does not assert the converse characterization of all Sturmian words."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/Mechanical/MechanicalBalance")),
        ]));
}
