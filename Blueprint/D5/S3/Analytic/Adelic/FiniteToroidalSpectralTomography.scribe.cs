using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class FiniteToroidalSpectralTomographyDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compact spectral window admits a finite normalized toroidal-period family "
            + "that detects both xi zeros and their multiplicities.",
        H("Finite Toroidal Spectral Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-toroidal-spectral-tomography"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/FiniteToroidalSpectralTomography."
                        + "finite_toroidal_spectral_tomography"),
                H("Finite toroidal families detect zeros and multiplicities"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The twist-nonvanishing loci cover the compact window. The frozen "
                            + "finite-frame theorem supplies one finite selected subfamily "
                            + "that remains pointwise nonvanishing on that window.")),
                    Paragraph(Text(
                        "Each normalized period is constructed as xiReading times its twist. "
                            + "The selected common-zero set therefore equals the xi zero set "
                            + "inside the window.")),
                    Paragraph(Text(
                        "At every point, all selected product orders dominate the xi order, "
                            + "and the selected nonzero twist realizes equality. Thus the "
                            + "finite indexed infimum is the asserted minimum."))),
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
        Formula window = F.Id("K");
        Formula twist = F.Id("T");
        Formula selected = F.Id("I");
        Formula index = F.Id("i");
        Formula point = F.Id("s");
        Formula rho = F.Id("rho");
        Formula xi = F.Id("xiReading");
        Formula familyType = Arrow(indexType, Arrow(complex, complex));
        Formula windowType = Call("Set", complex);
        Formula twistAtPoint = Apply(Apply(twist, index), point);
        Formula periodFunction = Seq(xi, Sp, Times, Sp, Apply(twist, index));
        Formula periodAtPoint = Seq(
            Apply(xi, point), Sp, Times, Sp, twistAtPoint);

        Formula twistDifferentiable = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Call("Differentiable", complex, Apply(twist, index)));
        Formula pointwiseNonvanishing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Call("mem", point, window),
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [Bound("i", indexType)],
                    NotEqualTo(twistAtPoint, D(0)))));
        Formula premises = And(
            twistDifferentiable,
            And(Call("IsCompact", window), pointwiseNonvanishing));

        Formula allSelectedPeriodsZero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Implies(Call("mem", index, selected), EqualTo(periodAtPoint, D(0))));
        Formula commonZeroSet = Seq(
            OpenBrace, point, Sp, InMacro, Sp, window, Sp, Mid, Sp,
            allSelectedPeriodsZero, CloseBrace);
        Formula xiZeroSet = Seq(
            OpenBrace, point, Sp, InMacro, Sp, window, Sp, Mid, Sp,
            EqualTo(Apply(xi, point), D(0)), CloseBrace);
        Formula zeroSetIdentity = EqualTo(commonZeroSet, xiZeroSet);

        Formula selectedMinimum = Call(
            "iInf",
            Seq(index, Sp, InMacro, Sp, selected),
            Call("analyticOrderAt", periodFunction, rho));
        Formula orderIdentity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", complex)],
            Implies(
                Call("mem", rho, window),
                EqualTo(Call("analyticOrderAt", xi, rho), selectedMinimum)));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("I", Call("Finset", indexType))],
            And(zeroSetIdentity, orderIdentity));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("K", windowType),
                Bound("T", familyType),
            ],
            Implies(premises, conclusion)));
    }
}
