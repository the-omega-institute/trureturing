using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.MetricGeometry;

internal sealed class GreenClassBudgetGeometryDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Asymptotics/MetricGeometry/GreenClassBudgetGeometry."
            + "green_class_budget_geometry";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform Green-class volume depends only on budget, while exact drift depends on the first gap.",
        H("Budget and First-Gap Geometry of Green Classes"),
        Blocks(Describe.Lean(
            DescribeId.Create("green-class-budget-geometry"),
            DeclarationHandle.Create(Declaration),
            H("Budget controls volume while the first hole controls drift"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let O be a finite nonempty nontrivial alphabet carrying the measurable discrete "
                        + "structure used by the uniform product law and the PiNat prefix metric. For a "
                        + "finite support S and target t, the Green class G(S,t) consists of all infinite "
                        + "strings agreeing with t on S.")),
                Paragraph(Text(
                    "Its uniform product measure is (card O)^(-1) raised to card S. Hence replacing S "
                        + "by any support U of the same cardinality leaves the volume unchanged: the "
                        + "regression budget sees how many coordinates were tested, not where they lie.")),
                Paragraph(Text(
                    "Its prefix-metric diameter is exactly (1/2)^firstHole(S), so the least untested "
                        + "coordinate fixes the full drift radius regardless of tests placed later. At "
                        + "fixed budget, (1/2)^card(S) is the smallest possible diameter, and equality "
                        + "holds exactly when S is the gapless prefix range(card(S)).")),
                Paragraph(Text(
                    "The proof applies the frozen canonical Green-class measure, exact-diameter, and "
                        + "prefix-extremality theorems. It introduces no replacement Green class, measure, "
                        + "metric, or first-hole definition."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula alphabet = F.Id("O");
        Formula support = F.Id("S");
        Formula otherSupport = F.Id("U");
        Formula target = F.Id("t");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finsetNaturals = Seq(
            Operatorname, Grp(F.Id("Finset")), Open, naturals, Close);
        Formula green = Seq(
            F.Id("G"), Open, support, Comma, Sp, target, Close);
        Formula otherGreen = Seq(
            F.Id("G"), Open, otherSupport, Comma, Sp, target, Close);
        Formula cardAlphabet = Seq(
            Operatorname, Grp(F.Id("card")), Open, alphabet, Close);
        Formula cardSupport = Seq(
            Operatorname, Grp(F.Id("card")), Open, support, Close);
        Formula cardOtherSupport = Seq(
            Operatorname, Grp(F.Id("card")), Open, otherSupport, Close);
        Formula measure = Seq(
            Operatorname, Grp(F.Id("stringMeasure")), Open,
            alphabet, Comma, Sp, green, Close);
        Formula otherMeasure = Seq(
            Operatorname, Grp(F.Id("stringMeasure")), Open,
            alphabet, Comma, Sp, otherGreen, Close);
        Formula diameter = Seq(
            Operatorname, Grp(F.Id("diam")), Open, green, Close);
        Formula firstHole = Seq(
            Operatorname, Grp(F.Id("firstHole")), Open, support, Close);
        Formula budgetMass = Seq(
            Open, cardAlphabet, Caret, Grp(Minus, D(1)), Close,
            Caret, Grp(cardSupport));
        Formula firstHoleRadius = Seq(
            Frac, Grp(D(1)), Grp(D(2)), Caret, Grp(firstHole));
        Formula budgetRadius = Seq(
            Frac, Grp(D(1)), Grp(D(2)), Caret, Grp(cardSupport));
        Formula prefix = Seq(
            Operatorname, Grp(F.Id("range")), Open, cardSupport, Close);
        Formula instances = Seq(
            Operatorname, Grp(F.Id("Fintype")), Open, alphabet, Close, Sp, Land, Sp,
            Operatorname, Grp(F.Id("Nonempty")), Open, alphabet, Close, Sp, Land, Sp,
            Operatorname, Grp(F.Id("MeasurableSpace")), Open, alphabet, Close, Sp, Land, Sp,
            Operatorname, Grp(F.Id("MeasurableSingletonClass")), Open, alphabet, Close,
            Sp, Land, RowBreak, Grp(),
            Operatorname, Grp(F.Id("TopologicalSpace")), Open, alphabet, Close, Sp, Land, Sp,
            Operatorname, Grp(F.Id("DiscreteTopology")), Open, alphabet, Close, Sp, Land, Sp,
            Operatorname, Grp(F.Id("Nontrivial")), Open, alphabet, Close);
        Formula supportInvariance = Seq(
            Forall, Sp, otherSupport, Colon, Sp, finsetNaturals, Comma, Sp,
            cardOtherSupport, Sp, Eq, Sp, cardSupport, Sp, Rightarrow, Sp,
            otherMeasure, Sp, Eq, Sp, measure);
        Formula prefixExtremality = Seq(
            budgetRadius, Sp, Le, Sp, diameter, Sp, Land, Sp,
            Open, diameter, Sp, Eq, Sp, budgetRadius, Sp, Iff, Sp,
            support, Sp, Eq, Sp, prefix, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, alphabet, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            instances, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, support, Colon, Sp, finsetNaturals, Comma, Sp,
            target, Colon, Sp, naturals, Sp, To, Sp, alphabet, Comma,
            RowBreak, Grp(),
            measure, Sp, Eq, Sp, budgetMass, Sp, Land,
            RowBreak, Grp(),
            Open, supportInvariance, Close, Sp, Land,
            RowBreak, Grp(),
            diameter, Sp, Eq, Sp, firstHoleRadius, Sp, Land,
            RowBreak, Grp(),
            Open, prefixExtremality, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
