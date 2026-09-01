using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Toroidal;

internal sealed class ToroidalProvenanceCutDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Toroidal/ToroidalProvenanceCut."
            + "toroidal_provenance_cut";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A selected nonzero twist makes period vanishing equivalent to base vanishing.",
        H("Toroidal Provenance Cut"),
        Blocks(Describe.Lean(
            DescribeId.Create("toroidal-provenance-cut"),
            DeclarationHandle.Create(Declaration),
            H("A nonzero twist separates base zeros from twist zeros"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The profile retains the selected finite index set and filters it twice "
                        + "at the chosen point: once by period vanishing and once by twist "
                        + "vanishing. The theorem earns that profile definition by giving its "
                        + "per-index membership cut under the displayed factorization.")),
                Paragraph(Text(
                    "This result is distinct from ToroidalCommonZeroLocus, "
                        + "ToroidalObserverSetCover, ToroidalTemperednessCriterion, and "
                        + "ToroidalJetDepth. Those neighbouring modules concern global, "
                        + "observer, or jet statements; they are context rather than "
                        + "dependencies of this Mathlib-generic cut.")),
                Paragraph(Text(
                    "The nonzero-twist certificate is the C-5 chart-selection precondition: "
                        + "a chart must be chosen where twist is nonzero before projective jet "
                        + "normalization. The same provenance distinction supplies the A-R5 "
                        + "residual cut between a base zero and a twist zero."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula indexType = F.Id("Index");
        Formula pointType = F.Id("Point");
        Formula scalarType = F.Id("Scalar");
        Formula selected = F.Id("selected");
        Formula period = F.Id("period");
        Formula twist = F.Id("twist");
        Formula baseValue = F.Id("base");
        Formula point = F.Id("s");
        Formula index = F.Id("i");
        Formula zero = D(0);
        Formula familyType = Arrow(indexType, Arrow(pointType, scalarType));
        Formula profile = Call(
            "toroidalVanishingProfile", selected, period, twist, point);
        Formula periodAtPoint = Apply(Apply(period, index), point);
        Formula twistAtPoint = Apply(Apply(twist, index), point);
        Formula baseAtPoint = Apply(baseValue, point);
        Formula periodMembership = Call(
            "mem", index, Call("periodZero", profile));
        Formula twistMembership = Call(
            "mem", index, Call("twistZero", profile));

        Formula hypotheses = And(
            Call("mem", index, selected),
            And(
                EqualTo(
                    periodAtPoint,
                    Seq(baseAtPoint, Sp, Times, Sp, twistAtPoint)),
                NotEqualTo(twistAtPoint, zero)));
        Formula conclusion = And(
            Iff(periodMembership, EqualTo(baseAtPoint, zero)),
            new Formula.Not(twistMembership));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("Point", type),
                Bound("Scalar", type),
                Bound("indexDecision", Call("DecidableEq", indexType)),
                Bound("scalarDecision", Call("DecidableEq", scalarType)),
                Bound("mulZero", Call("MulZeroClass", scalarType)),
                Bound("noZeroDivisors", Call("NoZeroDivisors", scalarType)),
                Bound("selected", Call("Finset", indexType)),
                Bound("period", familyType),
                Bound("twist", familyType),
                Bound("base", Arrow(pointType, scalarType)),
                Bound("s", pointType),
                Bound("i", indexType),
            ],
            Implies(hypotheses, conclusion)));
    }
}
