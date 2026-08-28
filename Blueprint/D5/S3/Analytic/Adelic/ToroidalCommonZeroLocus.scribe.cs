using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ToroidalCommonZeroLocusDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise nonvanishing quadratic twists identify the common period-zero locus "
            + "with the completed-zeta zero locus on the regular spectral domain.",
        H("Toroidal Common Zero Locus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("toroidal-common-zero-locus"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/ToroidalCommonZeroLocus."
                        + "toroidal_common_zero_locus"),
                H("All quadratic-period readouts have exactly the xi common zeros"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The set Omega is the source's regular spectral region. Period and "
                            + "twist are complex-valued families on the exact complex carrier, "
                            + "and the displayed factorization constructs every period readout "
                            + "as xiReading times its quadratic twist.")),
                    Paragraph(Text(
                        "Pointwise nonvanishing means that every point of Omega has at least "
                            + "one twist chart on which cancellation by the twist is valid. "
                            + "The common period-zero set is therefore exactly the xiReading "
                            + "zero set on the subtype Omega."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula complex = Call("Complex");
        Formula indexType = F.Id("Index");
        Formula omega = F.Id("Omega");
        Formula period = F.Id("P");
        Formula twist = F.Id("T");
        Formula index = F.Id("i");
        Formula spectralPoint = F.Id("s");
        Formula subtypePoint = F.Id("x");
        Formula pointValue = Call("val", subtypePoint);
        Formula familyType = Arrow(indexType, Arrow(complex, complex));
        Formula omegaType = Call("Set", complex);
        Formula omegaSubtype = Call("Subtype", omega);

        Formula periodAt(Formula i, Formula point) =>
            Apply(Apply(period, i), point);
        Formula twistAt(Formula i, Formula point) =>
            Apply(Apply(twist, i), point);

        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("s", complex)],
            EqualTo(
                periodAt(index, spectralPoint),
                Seq(
                    Apply(F.Id("xiReading"), spectralPoint), Sp, Times, Sp,
                    twistAt(index, spectralPoint))));
        Formula cover = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Call("mem", spectralPoint, omega),
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [Bound("i", indexType)],
                    NotEqualTo(twistAt(index, spectralPoint), D(0)))));
        Formula commonPeriodZero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            EqualTo(periodAt(index, pointValue), D(0)));
        Formula xiZero = EqualTo(Apply(F.Id("xiReading"), pointValue), D(0));
        Formula periodZeroLocus =
            new Formula.SetBuilder(commonPeriodZero, subtypePoint, omegaSubtype);
        Formula xiZeroLocus =
            new Formula.SetBuilder(xiZero, subtypePoint, omegaSubtype);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("Omega", omegaType),
                Bound("P", familyType),
                Bound("T", familyType),
            ],
            Implies(
                And(factorization, cover),
                EqualTo(periodZeroLocus, xiZeroLocus))));
    }
}
