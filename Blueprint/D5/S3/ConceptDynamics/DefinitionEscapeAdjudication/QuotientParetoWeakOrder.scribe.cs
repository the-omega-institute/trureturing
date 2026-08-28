using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class QuotientParetoWeakOrderDocument : IScribeDocumentDefinition
{
    private enum CoordinateOrder
    {
        LessOrEqual,
        Preorder,
    }

    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Existential weak Pareto dominance on explicit finite classes is representative-independent, decidable by a finite scan, and a partial order.",
        H("Decidable Weak Pareto Order on the Finite Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quotient-pareto-weak"),
                DeclarationHandle.Create(DeclarationPrefix + "QuotientParetoWeak"),
                H("Existential representative relation"),
                StatementSource.FromAuthor(RelationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A class weakly dominates another when one representative pair satisfies "
                        + "the existing carrier-level ParetoWeakOn relation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quotient-pareto-weak-scan"),
                DeclarationHandle.Create(DeclarationPrefix + "quotientParetoWeakScan"),
                H("Finite product scan"),
                StatementSource.FromAuthor(ScanFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The decision procedure forms the finite product of the two explicit "
                        + "classes, filters it by ParetoWeakOn, and decides nonemptiness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quotient-pareto-weak-decidable"),
                DeclarationHandle.Create(DeclarationPrefix + "quotientParetoWeakDecidable"),
                H("Finite-scan decidability"),
                StatementSource.FromAuthor(DecisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Correctness of the product scan supplies a Decidable term for the "
                        + "quotient relation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quotient-pareto-weak-finite-partial-order"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "quotient_pareto_weak_finite_decidable_partial_order"),
                H("Representative-independent decidable partial order"),
                StatementSource.FromAuthor(OrderTheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "One dominating representative pair implies that every pair dominates: "
                            + "members of one explicit class are related by the symmetric "
                            + "Pareto kernel, so the frozen weak-preorder laws transport the "
                            + "comparison between representatives.")),
                    Paragraph(Text(
                        "The same transport proves transitivity and antisymmetry. Reflexivity "
                            + "uses the proved nonemptiness of every quotient class. If the "
                            + "action carrier is empty, the quotient has no element and the "
                            + "quantified relation statement is vacuous; no artificial element "
                            + "is introduced."))),
                DescribeRole.Theorem))));

    private static Formula GainVector() => Call(
        "GainVector", F.Id("Information"), F.Id("Residual"), F.Id("Transfer"),
        F.Id("Cost"), F.Id("Risk"));

    private static Formula Carrier(Formula finiteCarrier) =>
        Call("ParetoCarrier", finiteCarrier);

    private static Formula Quotient(Formula value, Formula finiteCarrier) =>
        Call("FiniteParetoQuotient", value, finiteCarrier);

    private static Formula ClassValue(Formula quotientClass) =>
        Call("val", quotientClass);

    private static Formula WeakOn(
        Formula value, Formula finiteCarrier, Formula left, Formula right) =>
        Call("ParetoWeakOn", value, finiteCarrier, left, right);

    private static Formula QuotientWeak(
        Formula value, Formula finiteCarrier, Formula left, Formula right) =>
        Call("QuotientParetoWeak", value, finiteCarrier, left, right);

    private static Formula Scan(
        Formula value, Formula finiteCarrier, Formula left, Formula right) =>
        Call("quotientParetoWeakScan", value, finiteCarrier, left, right);

    private static Formula DecidableOrder(Formula type) =>
        Seq(
            OpenBracket,
            Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Colon, Sp, type,
            Comma, Sp,
            Call("Decidable", Seq(F.Id("a"), Sp, Leq, Sp, F.Id("b"))),
            CloseBracket);

    private static Formula CoordinateConstraint(CoordinateOrder order, Formula type) =>
        order switch
        {
            CoordinateOrder.LessOrEqual => Call("LE", type),
            CoordinateOrder.Preorder => Call("Preorder", type),
            _ => throw new ArgumentOutOfRangeException(nameof(order)),
        };

    private static Formula AssumptionPrefix(CoordinateOrder order)
    {
        Formula action = F.Id("Action");
        Formula information = F.Id("Information");
        Formula residual = F.Id("Residual");
        Formula transfer = F.Id("Transfer");
        Formula cost = F.Id("Cost");
        Formula risk = F.Id("Risk");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Seq(
            Forall, Sp, action, Comma, Sp, information, Comma, Sp, residual,
            Comma, Sp, transfer, Comma, Sp, cost, Comma, Sp, risk, Colon, Sp,
            type, Comma, RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", action), CloseBracket, Comma, Sp,
            OpenBracket, CoordinateConstraint(order, information), CloseBracket,
            Comma, Sp,
            OpenBracket, CoordinateConstraint(order, residual), CloseBracket,
            Comma, Sp,
            OpenBracket, CoordinateConstraint(order, transfer), CloseBracket,
            Comma, Sp,
            OpenBracket, CoordinateConstraint(order, cost), CloseBracket,
            Comma, Sp,
            OpenBracket, CoordinateConstraint(order, risk), CloseBracket,
            Comma, RowBreak, Grp(),
            DecidableOrder(information), Comma, Sp, DecidableOrder(residual),
            Comma, Sp, DecidableOrder(transfer), Comma, RowBreak, Grp(),
            DecidableOrder(cost), Comma, Sp, DecidableOrder(risk), Comma,
            RowBreak, Grp(),
            F.Id("value"), Colon, Sp, action, Sp, To, Sp, GainVector(), Comma, Sp,
            F.Id("F"), Colon, Sp, Call("Finset", action), Comma,
            RowBreak, Grp());
    }

    private static Formula RelationFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula c = F.Id("C");
        Formula d = F.Id("D");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula quotient = Quotient(value, finiteCarrier);
        Formula carrier = Carrier(finiteCarrier);
        Formula representativePair = Seq(
            Exists, Sp, x, Colon, Sp, carrier, Comma, Sp,
            x, Sp, InMacro, Sp, ClassValue(c), Sp, Land, Sp,
            Exists, Sp, y, Colon, Sp, carrier, Comma, Sp,
            y, Sp, InMacro, Sp, ClassValue(d), Sp, Land, Sp,
            WeakOn(value, finiteCarrier, x, y));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            AssumptionPrefix(CoordinateOrder.LessOrEqual),
            c, Comma, Sp, d, Colon, Sp, quotient, Comma, RowBreak, Grp(),
            QuotientWeak(value, finiteCarrier, c, d), Sp, Iff, Sp,
            representativePair, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ScanFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula c = F.Id("C");
        Formula d = F.Id("D");
        Formula pair = F.Id("p");
        Formula quotient = Quotient(value, finiteCarrier);
        Formula candidatePairs = Call("product", ClassValue(c), ClassValue(d));
        Formula filteredPairs = Call(
            "filter", candidatePairs,
            Seq(LambdaLower, Sp, pair, Comma, Sp,
                WeakOn(value, finiteCarrier, Call("fst", pair), Call("snd", pair))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            AssumptionPrefix(CoordinateOrder.LessOrEqual),
            c, Comma, Sp, d, Colon, Sp, quotient, Comma, RowBreak, Grp(),
            Scan(value, finiteCarrier, c, d), Sp, Eq, Sp,
            Call("decide", Call("Nonempty", filteredPairs)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula DecisionFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula c = F.Id("C");
        Formula d = F.Id("D");
        Formula quotient = Quotient(value, finiteCarrier);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            AssumptionPrefix(CoordinateOrder.Preorder),
            c, Comma, Sp, d, Colon, Sp, quotient, Comma, RowBreak, Grp(),
            Call("quotientParetoWeakDecidable", value, finiteCarrier, c, d),
            Colon, Sp,
            Call("Decidable", QuotientWeak(value, finiteCarrier, c, d)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula OrderTheoremFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula c = F.Id("C");
        Formula d = F.Id("D");
        Formula e = F.Id("E");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula quotient = Quotient(value, finiteCarrier);
        Formula carrier = Carrier(finiteCarrier);
        Formula representativeIndependent = Seq(
            Forall, Sp, c, Comma, Sp, d, Colon, Sp, quotient, Comma, Sp,
            QuotientWeak(value, finiteCarrier, c, d), Sp, Iff, Sp,
            Forall, Sp, x, Colon, Sp, carrier, Comma, Sp,
            x, Sp, InMacro, Sp, ClassValue(c), Sp, Rightarrow, Sp,
            Forall, Sp, y, Colon, Sp, carrier, Comma, Sp,
            y, Sp, InMacro, Sp, ClassValue(d), Sp, Rightarrow, Sp,
            WeakOn(value, finiteCarrier, x, y));
        Formula scanCorrect = Seq(
            Forall, Sp, c, Comma, Sp, d, Colon, Sp, quotient, Comma, Sp,
            Scan(value, finiteCarrier, c, d), Sp, Eq, Sp, F.Id("true"),
            Sp, Iff, Sp, QuotientWeak(value, finiteCarrier, c, d));
        Formula decisionAvailable = Seq(
            Forall, Sp, c, Comma, Sp, d, Colon, Sp, quotient, Comma, Sp,
            Call("Nonempty", Call(
                "Decidable", QuotientWeak(value, finiteCarrier, c, d))));
        Formula reflexive = Seq(
            Forall, Sp, c, Colon, Sp, quotient, Comma, Sp,
            QuotientWeak(value, finiteCarrier, c, c));
        Formula transitive = Seq(
            Forall, Sp, c, Comma, Sp, d, Comma, Sp, e, Colon, Sp, quotient,
            Comma, Sp,
            QuotientWeak(value, finiteCarrier, c, d), Sp, Rightarrow, Sp,
            QuotientWeak(value, finiteCarrier, d, e), Sp, Rightarrow, Sp,
            QuotientWeak(value, finiteCarrier, c, e));
        Formula antisymmetric = Seq(
            Forall, Sp, c, Comma, Sp, d, Colon, Sp, quotient, Comma, Sp,
            QuotientWeak(value, finiteCarrier, c, d), Sp, Rightarrow, Sp,
            QuotientWeak(value, finiteCarrier, d, c), Sp, Rightarrow, Sp,
            c, Sp, Eq, Sp, d);
        Formula emptyVacuous = Seq(
            finiteCarrier, Sp, Eq, Sp, Emptyset, Sp, Rightarrow, Sp,
            Forall, Sp, c, Comma, Sp, d, Colon, Sp, quotient, Comma, Sp,
            QuotientWeak(value, finiteCarrier, c, d));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            AssumptionPrefix(CoordinateOrder.Preorder),
            Open, representativeIndependent, Close, Sp, Land, RowBreak, Grp(),
            Open, scanCorrect, Close, Sp, Land, RowBreak, Grp(),
            Open, decisionAvailable, Close, Sp, Land, RowBreak, Grp(),
            Open, reflexive, Close, Sp, Land, RowBreak, Grp(),
            Open, transitive, Close, Sp, Land, RowBreak, Grp(),
            Open, antisymmetric, Close, Sp, Land, RowBreak, Grp(),
            Open, emptyVacuous, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
