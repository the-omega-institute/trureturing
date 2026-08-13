using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class MechanicalComplexityCharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Characterize irrational lower mechanical slopes simultaneously by exact factor "
            + "complexity and failure of eventual periodicity.",
        H("The Lower Mechanical Complexity Characterization"),
        Blocks(
            Paragraph(Text(
                "Fix a real slope alpha in the half-open interval from zero to one and an "
                + "arbitrary real intercept rho. Factors begin at natural indices, and eventual "
                + "periodicity uses the repository's one-sided natural-tail convention.")),
            Describe.Lean(
                DescribeId.Create("period-bounds-factor-complexity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalComplexityCharacterization."
                        + "lower_mechanical_factor_set_card_le_period"),
                H("A positive period bounds every factor count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("p"), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Periodic")), Open,
                    F.Id("w"), Underscore, Grp(Alpha, Comma, Rho), Comma, F.Id("p"), Close,
                    Sp, Rightarrow, Sp, Forall, Sp, F.Id("n"), InMacro, Mathbb,
                    Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("card")), Open,
                    F.Id("FactorSet"), Open, Alpha, Comma, Rho, Comma, F.Id("n"), Close,
                    Close, Sp, Leq, Sp, F.Id("p")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Periodicity is lifted pointwise through each finite factor. Reducing every "
                    + "start modulo p shows that all occurring factors are represented among the "
                    + "first p starts, and the cardinality of an image cannot exceed its domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-complexity-characterizes-irrationality"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalComplexityCharacterization."
                        + "lower_mechanical_factor_complexity_iff_irrational"),
                H("Exact n plus one complexity is equivalent to irrationality"),
                StatementSource.FromAuthor(Disp(Seq(
                    OpenBracket, Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")),
                    Comma, Sp, Operatorname, Grp(F.Id("card")), Open,
                    F.Id("FactorSet"), Open, Alpha, Comma, Rho, Comma, F.Id("n"), Close,
                    Close, Sp, Eq, Sp, F.Id("n"), Sp, Plus, Sp, D(1), CloseBracket,
                    Sp, Iff, Sp, Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The forward implication excludes every rational slope. Its reduced "
                        + "denominator p is a positive period, so the factor count at length p is "
                        + "at most p rather than p plus one.")),
                    Paragraph(Text(
                        "The reverse implication is the frozen irrational lower-mechanical "
                        + "factor-complexity theorem, applied at every length."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-mechanical-three-way-characterization"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalComplexityCharacterization."
                        + "lower_mechanical_factor_complexity_iff_irrational_iff_not_eventuallyPeriodic"),
                H("Complexity, irrationality, and aperiodicity coincide"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Alpha, Comma, Rho, InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    D(0), Sp, Leq, Sp, Alpha, Sp, Lt, Sp, D(1), Comma, Sp,
                    Open, OpenBracket, Forall, Sp, F.Id("n"), InMacro, Mathbb,
                    Grp(F.Id("N")), Comma, Sp, Operatorname, Grp(F.Id("card")), Open,
                    F.Id("FactorSet"), Open, Alpha, Comma, Rho, Comma, F.Id("n"), Close,
                    Close, Sp, Eq, Sp, F.Id("n"), Sp, Plus, Sp, D(1), CloseBracket,
                    Sp, Iff, Sp, Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close,
                    Close, Sp, Land, Sp,
                    Open, Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close,
                    Sp, Iff, Sp, Neg, Operatorname, Grp(F.Id("EventuallyPeriodic")), Open,
                    F.Id("w"), Underscore, Grp(Alpha, Comma, Rho), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first equivalence is the new rational-factor exclusion. The second is "
                    + "obtained by negating the frozen equivalence between rationality and "
                    + "eventual periodicity. Together they state the requested three-way "
                    + "classification without changing either frozen convention."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/Mechanical/MechanicalFactorComplexity")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/Mechanical/MechanicalPeriodicity")),
        ]));
}
