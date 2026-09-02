using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ShiftedXiPoisson;

internal sealed class ShiftedPoissonSemigroupDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup."
            + "shifted_poisson_semigroup";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Increasing the shift of the finite xi-zero phase density is exactly concrete "
            + "Poisson convolution.",
        H("Unconditional Shifted-Poisson Flow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unconditional-shifted-poisson-flow"),
                DeclarationHandle.Create(Declaration),
                H("Larger shifts are exactly Poisson smoothing"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a positive-height finite window containing exactly the positive-"
                            + "ordinate zeros of the repository's canonical xi reading. Each "
                            + "distinct zero is repeated by its concrete analytic vanishing "
                            + "order in the phase-density measure.")),
                    Paragraph(Text(
                        "For omega at least one half and nonnegative eta, both public conjuncts "
                            + "state the same concrete measure identity: the density at omega "
                            + "plus eta is convolution of the eta Poisson kernel with the "
                            + "density at omega. The first leaf carries formula (347.7); the "
                            + "second carries the separately boxed smoothing conclusion.")),
                    Paragraph(Text(
                        "The Poisson kernel is the scaled half-Cauchy probability measure, and "
                            + "convolution is Mathlib measure convolution. Characteristic-"
                            + "function uniqueness proves its additive semigroup law.")),
                    Paragraph(Text(
                        "The named shiftedPhaseFourier carrier evaluates the characteristic "
                            + "function at minus t, exactly matching the source convention. Its "
                            + "factorization is exp(-omega times abs(t)) times the independently "
                            + "defined finite zero sum Q_T; Q_T contains the delta and ordinate "
                            + "factors and has no omega parameter. The main equality is proved "
                            + "through this certificate.")),
                    Paragraph(Text(
                        "The canonicalShiftedZeroWindow constructor takes the finite set of all "
                            + "canonical xi zeros with ordinates in (0,T], and analytic order "
                            + "provides multiplicity. The local library does not exhibit a "
                            + "concrete zeta zero, so the supporting noncollapse theorem states "
                            + "the source-grounded window-nonemptiness condition explicitly and "
                            + "then separates a concrete pair of densities without caller-supplied "
                            + "zero coordinates. No Riemann-hypothesis or inverse-positivity premise "
                            + "occurs in either public equality leaf."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula t = F.Id("T");
        Formula omega = F.Id("omega");
        Formula eta = F.Id("eta");
        Formula window = F.Id("window");
        Formula shifted = Call(
            "shiftedPhaseDensity",
            window,
            Add(omega, eta));
        Formula original = Call("shiftedPhaseDensity", window, omega);
        Formula kernel = Call("poissonKernel", Call("toNNReal", eta));
        Formula convolution = Call("conv", kernel, original);
        Formula equality = Equal(shifted, convolution);
        Formula conclusions = new Formula.Logic(
            equality,
            FormulaLogicOperator.And,
            equality);
        Formula bounds = new Formula.Logic(
            new Formula.Relation(
                new Formula.Fraction(D(1), D(2)),
                FormulaRelationOperator.LessThanOrEqual,
                omega),
            FormulaLogicOperator.And,
            new Formula.Relation(
                D(0),
                FormulaRelationOperator.LessThanOrEqual,
                eta));
        Formula theoremBody = new Formula.Logic(
            bounds,
            FormulaLogicOperator.Implies,
            conclusions);
        Formula quantifiedWindow = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("window"),
            Call("ShiftedZeroWindow", t),
            theoremBody);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("T"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("omega"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("eta"), real),
            ],
            quantifiedWindow));
    }

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
