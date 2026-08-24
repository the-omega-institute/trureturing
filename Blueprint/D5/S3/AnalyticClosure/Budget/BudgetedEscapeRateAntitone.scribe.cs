using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Budget;

internal sealed class BudgetedEscapeRateAntitoneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Budgeted escape rates lie in the unit interval and are antitone in budget.",
        H("Budgeted Escape Rate Bounds and Antitonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("budgeted-escape-rate-bounds-and-antitonicity"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone."
                        + "budgeted_escape_rate_bounds_and_antitone"),
                H("Budgeted escape rates are bounded and antitone"),
                StatementSource.FromAuthor(NormalizationBoundsAndAntitoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A supplement strategy is feasible at budget L when its cost is at "
                            + "most L. Its escape value is the mass assigned to the canonical "
                            + "target-defect relation of the joined base and supplement "
                            + "readout, divided by the mass M0 of the base target-defect "
                            + "relation. This denominator is part of the public definition, "
                            + "not a caller-supplied parameter. The budgeted "
                            + "escape rate is the real infimum of these feasible normalized "
                            + "values.")),
                    Paragraph(Text(
                        "The public weight type requires zero mass for the empty set and "
                            + "nonnegative mass for every set. Escape mass bounded above by M0 "
                            + "then places every normalized feasible value in the unit interval. "
                            + "Nonemptiness of the first feasible-value set remains explicit; "
                            + "nonnegativity and positivity derive zero as a lower bound for each "
                            + "value set inside the Lean proof.")),
                    Paragraph(Text(
                        "When L1 is at most L2, every strategy feasible at L1 is feasible at "
                            + "L2. The larger value set therefore has an infimum no greater than "
                            + "the smaller value set, which gives the asserted antitonicity."))),
                DescribeRole.Theorem))));

    private static Formula Rate(Formula budget) => Seq(
        Rho, Underscore, Grp(Gamma), Open, budget, Close);

    private static Formula NormalizationBoundsAndAntitoneFormula()
    {
        Formula budget = F.Id("L");
        Formula first = Seq(F.Id("L"), Underscore, Grp(D(1)));
        Formula second = Seq(F.Id("L"), Underscore, Grp(D(2)));
        Formula strategy = GammaLower;
        Formula baseline = F.Id("base");
        Formula target = F.Id("target");
        Formula supplement = Call("supplement", strategy);
        Formula baselineDefect = Call("defectRelation", baseline, target);
        Formula supplementedDefect = Call(
            "defectRelation", Call("conceptJoin", baseline, supplement), target);
        Formula baselineMass = Seq(F.Id("M"), Underscore, Grp(D(0)));
        Formula mass = Seq(Mu, Open, supplementedDefect, Close);
        Formula normalizer = Seq(Mu, Open, baselineDefect, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            baselineMass, Sp, Eq, Sp, normalizer, Sp, Gt, Sp, D(0), Comma,
            RowBreak,
            Rate(budget), Sp, Eq, Sp, Call("sInf", Seq(
                OpenBrace,
                Frac, Grp(mass), Grp(normalizer), Sp, Mid, Sp,
                Call("cost", strategy), Sp, Le, Sp, budget,
                CloseBrace)), Comma,
            RowBreak,
            D(0), Sp, Le, Sp, Rate(budget), Sp, Le, Sp, D(1), Comma,
            RowBreak,
            first, Sp, Le, Sp, second, Sp, Rightarrow, Sp,
            Rate(second), Sp, Le, Sp, Rate(first), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
