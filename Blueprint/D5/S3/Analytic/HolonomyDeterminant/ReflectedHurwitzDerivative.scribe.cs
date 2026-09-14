using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HolonomyDeterminant;

internal sealed class ReflectedHurwitzDerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/HolonomyDeterminant/ReflectedHurwitzDerivative.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lerch's formula determines both reflected Hurwitz derivatives at zero.",
        H("Reflected Hurwitz derivative at zero"),
        Blocks(Describe.Lean(
            DescribeId.Create("reflected-hurwitz-derivative-at-zero"),
            DeclarationHandle.Create(Prefix + "has_reflected_hurwitz_derivative_at_zero_formula"),
            H("Lerch's formula on the open unit interval"),
            StatementSource.FromAuthor(LerchFormula()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/nist2026lerch")),
            Blocks(Paragraph(Text(
                "Let a be real with 0<a<1. The derivative is taken in the complex zeta "
                    + "argument. Subtract the Riemann partial sum from the Hurwitz partial "
                    + "sum and add (1-a)N to the power -s. The increments are interpolation "
                    + "remainders, bounded by 24 times N to the power -3/2 on the disk "
                    + "|s-1|<3/2. Uniform convergence and analytic continuation identify "
                    + "the limit with the zeta difference. Holomorphic derivative convergence "
                    + "and the Bohr-Mollerup limit give log Gamma. The Riemann derivative "
                    + "at zero supplies the constant. Applying the formula at 1-a gives "
                    + "the reflected sector, since 1-a and -a represent the same point "
                    + "of the additive circle."))),
            DescribeRole.Theorem))));

    private static Formula LerchFormula()
    {
        Formula a = F.Id("a");
        Formula reflected = Seq(D(1), Sp, Minus, Sp, a);
        Formula interval = new Formula.Logic(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, a),
            FormulaLogicOperator.And,
            new Formula.Relation(a, FormulaRelationOperator.LessThan, D(1)));
        Formula pair = new Formula.Logic(At(a), FormulaLogicOperator.And, At(reflected));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("a"), Seq(Mathbb, Grp(F.Id("R"))))],
            new Formula.Logic(interval, FormulaLogicOperator.Implies, pair)));
    }

    private static Formula At(Formula a) => new Formula.Relation(
        Call("zetaPrime", D(0), a), FormulaRelationOperator.Equal,
        Seq(Call("log", Call("Gamma", a)), Sp, Minus, Sp,
            new Formula.Fraction(Call("log", Seq(D(2), Sp, Times, Sp, Pi)), D(2))));
}
