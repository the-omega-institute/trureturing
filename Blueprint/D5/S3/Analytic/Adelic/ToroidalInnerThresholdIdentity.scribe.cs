using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ToroidalInnerThresholdIdentityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common toroidal escape threshold equals the eventual-innerness threshold, "
            + "and both vanish exactly on the completed-zeta critical line.",
        H("Toroidal Inner Threshold Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("toroidal-inner-threshold-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/ToroidalInnerThresholdIdentity."
                        + "toroidal_inner_threshold_identity"),
                H("Toroidal escape and eventual innerness have one critical width"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The deviation set is constructed from right-half-plane spectral points "
                            + "invisible to every supplied period readout. Its supremum is the "
                            + "toroidal threshold. The inner candidate set is constructed from "
                            + "nonnegative widths beyond which every larger width is inner; its "
                            + "infimum is the inner threshold.")),
                    Paragraph(Text(
                        "Pointwise twist nonvanishing and the displayed factorization identify "
                            + "common period zeros with xiReading zeros. The Suzuki equivalence "
                            + "then identifies inner candidates with upper bounds of the deviation "
                            + "set, so the conditional-completeness infimum/supremum theorem gives "
                            + "the threshold equality.")),
                    Paragraph(Text(
                        "Nonemptiness and boundedness are explicit because real sSup and sInf are "
                            + "conditional. Reflection of xiReading turns the right-half threshold "
                            + "criterion into the displayed global critical-line predicate."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        Seq(left, Sp, Lt, Sp, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        Seq(left, Sp, Leq, Sp, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula prop = Call("Prop");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula indexType = F.Id("Index");
        Formula period = F.Id("P");
        Formula twist = F.Id("T");
        Formula innerAt = F.Id("innerAt");
        Formula index = F.Id("i");
        Formula point = F.Id("s");
        Formula width = F.Id("a");
        Formula largerWidth = F.Id("omega");
        Formula deviation = F.Id("d");
        Formula deviations = F.Id("D");
        Formula innerCandidates = F.Id("A");
        Formula toroidalThreshold = F.Id("omegaTor");
        Formula innerThreshold = F.Id("omegaIn");
        Formula criticalLine = F.Id("criticalLine");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula realPart = Call("re", point);
        Formula familyType = Arrow(indexType, Arrow(complex, complex));
        Formula innerType = Arrow(real, prop);

        Formula periodAt(Formula i, Formula s) => Apply(Apply(period, i), s);
        Formula twistAt(Formula i, Formula s) => Apply(Apply(twist, i), s);

        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("s", complex)],
            EqualTo(
                periodAt(index, point),
                Seq(
                    Apply(F.Id("xiReading"), point), Sp, Times, Sp,
                    twistAt(index, point))));
        Formula pointwiseNonvanishing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("i", indexType)],
                Seq(twistAt(index, point), Sp, Neq, Sp, D(0))));
        Formula allInnerBeyond = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("omega", real)],
            Implies(
                LessThan(width, largerWidth),
                Apply(innerAt, largerWidth)));
        Formula zeroFreePastWidth = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                EqualTo(Apply(F.Id("xiReading"), point), D(0)),
                LessThanOrEqual(realPart, Seq(half, Sp, Plus, Sp, width))));
        Formula suzukiEquivalence = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("a", real)],
            Implies(
                LessThanOrEqual(D(0), width),
                IffFormula(allInnerBeyond, zeroFreePastWidth)));
        Formula allPeriodsZero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            EqualTo(periodAt(index, point), D(0)));
        Formula deviationPredicate = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("s", complex)],
            And(
                LessThanOrEqual(half, realPart),
                And(
                    allPeriodsZero,
                    EqualTo(
                        deviation,
                        Seq(realPart, Sp, Minus, Sp, half)))));
        Formula deviationSet = new Formula.SetBuilder(
            deviationPredicate, deviation, real);
        Formula innerPredicate = And(
            LessThanOrEqual(D(0), width),
            allInnerBeyond);
        Formula innerSet = new Formula.SetBuilder(innerPredicate, width, real);
        Formula criticalPredicate = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                EqualTo(Apply(F.Id("xiReading"), point), D(0)),
                EqualTo(realPart, half)));
        Formula hypotheses = And(
            factorization,
            And(
                pointwiseNonvanishing,
                And(
                    suzukiEquivalence,
                    And(
                        Call("Nonempty", deviations),
                        Call("BddAbove", deviations)))));
        Formula conclusion = And(
            EqualTo(toroidalThreshold, innerThreshold),
            And(
                IffFormula(
                    criticalLine,
                    EqualTo(toroidalThreshold, D(0))),
                IffFormula(
                    criticalLine,
                    EqualTo(innerThreshold, D(0)))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, indexType, Sp, InMacro, Sp, type, Comma, RowBreak,
            period, Comma, Sp, twist, Colon, Sp, familyType, Comma, RowBreak,
            innerAt, Colon, Sp, innerType, Comma, RowBreak,
            deviations, Sp, Colon, Eq, Sp, deviationSet, Comma, RowBreak,
            toroidalThreshold, Sp, Colon, Eq, Sp,
            Call("sSup", deviations), Comma, RowBreak,
            innerCandidates, Sp, Colon, Eq, Sp, innerSet, Comma, RowBreak,
            innerThreshold, Sp, Colon, Eq, Sp,
            Call("sInf", innerCandidates), Comma, RowBreak,
            criticalLine, Sp, Colon, Eq, Sp, criticalPredicate, Comma, RowBreak,
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak,
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
