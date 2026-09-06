using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class CountableNormalJetCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Zeros/CountableNormalJetCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous normal-jet positivity is detected at rational ordinates.",
        H("Countable Normal-Jet Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuous-nonnegative-iff-rat"),
                DeclarationHandle.Create(Prefix + "continuous_nonnegative_iff_rat"),
                H("Continuous positivity is detected on the rationals"),
                StatementSource.FromAuthor(ContinuousCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a continuous real-valued function, nonnegativity at every real "
                        + "point is equivalent to nonnegativity at every rational point. "
                        + "The reverse implication extends the closed nonnegative condition "
                        + "from the dense range of the rational embedding."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countable-normal-jet-criterion"),
                DeclarationHandle.Create(Prefix + "countable_normal_jet_criterion"),
                H("Rational normal jets give a countable criterion and finite certificates"),
                StatementSource.FromAuthor(NormalJetCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the analytic bridge identifying the Riemann hypothesis with "
                            + "nonnegativity of every real normal jet, and assume continuity in "
                            + "the ordinate at each depth. The dense rational criterion then "
                            + "gives the countable equivalence.")),
                    Paragraph(Text(
                        "Negating that equivalence produces a rational ordinate q and a finite "
                            + "depth m with a negative jet. The imported normal-jet formula "
                            + "rewrites this witness as a finite signed factorial convolution "
                            + "of critical-xi derivatives from order zero through 2m.")),
                    Paragraph(Text(
                        "The real-axis RH characterization is not available in D5 or pinned "
                            + "Mathlib and is deliberately exposed as a premise. The theorem "
                            + "proves the countable reduction and finite-certificate step; it "
                            + "does not claim to establish that missing analytic criterion."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/NormalJetFormula")),
        ]));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula ContinuousCriterionFormula()
    {
        Formula real = Call("Real");
        Formula rational = Call("Rat");
        Formula f = F.Id("f");
        Formula t = F.Id("t");
        Formula q = F.Id("q");
        Formula realNonnegative = ForAll(
            [Bound("t", real)], LessOrEqual(D(0), Apply(f, t)));
        Formula rationalNonnegative = ForAll(
            [Bound("q", rational)], LessOrEqual(D(0), Apply(f, q)));

        return F.Disp(ForAll(
            [Bound("f", Arrow(real, real))],
            Implies(Call("Continuous", f),
                Iff(realNonnegative, rationalNonnegative))));
    }

    private static Formula NormalJetCriterionFormula()
    {
        Formula real = Call("Real");
        Formula rational = Call("Rat");
        Formula natural = Call("Nat");
        Formula rh = F.Id("RH");
        Formula t = F.Id("t");
        Formula q = F.Id("q");
        Formula m = F.Id("m");
        Formula j = F.Id("j");
        Formula criticalXi = F.Id("criticalXi");
        Formula twoM = Seq(D(2), m);
        Formula reflectedIndex = Seq(twoM, Sp, Minus, Sp, j);
        Formula jet(Formula point, Formula depth) => Call("normalJet", point, depth);
        Formula nonnegative(Formula point, Formula depth) =>
            LessOrEqual(D(0), jet(point, depth));
        Formula allRealJets = ForAll(
            [Bound("t", real), Bound("m", natural)], nonnegative(t, m));
        Formula allRationalJets = ForAll(
            [Bound("q", rational), Bound("m", natural)], nonnegative(q, m));
        Formula jetAtDepth = Seq(
            Open, t, Sp, Mapsto, Sp, jet(t, m), Close);
        Formula allJetsContinuous = ForAll(
            [Bound("m", natural)], Call("Continuous", jetAtDepth));

        Formula derivativeAtJ = Call("iteratedDeriv", j, criticalXi, q);
        Formula derivativeAtReflectedIndex = Call(
            "iteratedDeriv", reflectedIndex, criticalXi, q);
        Formula sign = Seq(
            Open, Minus, D(1), Close, Caret,
            Grp(Seq(m, Sp, Plus, Sp, j)));
        Formula denominator = Seq(
            Call("factorial", j), Sp, Cdot, Sp,
            Call("factorial", reflectedIndex));
        Formula summand = Seq(
            new Formula.Fraction(sign, denominator), Sp, Cdot, Sp,
            derivativeAtJ, Sp, Cdot, Sp, derivativeAtReflectedIndex);
        Formula convolution = Seq(
            Sum, Underscore, Grp(Seq(j, Eq, D(0))),
            Caret, Grp(twoM), Sp, summand);
        Formula finiteCertificate = Exists(
            [Bound("q", rational), Bound("m", natural)],
            Less(convolution, D(0)));

        Formula premises = And(Iff(rh, allRealJets), allJetsContinuous);
        Formula conclusion = And(
            Iff(rh, allRationalJets),
            Iff(new Formula.Not(rh), finiteCertificate));
        return F.Disp(Implies(premises, conclusion));
    }
}
