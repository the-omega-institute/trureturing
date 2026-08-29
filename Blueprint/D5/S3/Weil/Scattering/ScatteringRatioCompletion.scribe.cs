using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class ScatteringRatioCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scattering-ratio readings together with right-shift normalization determine the function.",
        H("Scattering-Ratio Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scattering-ratio-completion"),
                DeclarationHandle.Create(
                        "D5/S3/Weil/Scattering/ScatteringRatioCompletion."
                        + "scattering_ratio_completion"),
                H("Scattering ratios determine a normalized function"),
                StatementSource.FromAuthor(Disp(Formula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed hypotheses keep the source ratio observation explicit: "
                            + "the values of F and G are nonzero, their shifted ratios agree, "
                            + "and the quotient F(z+n)/G(z+n) tends to one along every right shift.")),
                    Paragraph(Text(
                        "Evaluating the ratio identity at (z+1)/2 gives one-step periodicity "
                            + "of F/G. Iteration and the right-shift limit force that quotient "
                            + "to equal one at every z, hence F=G."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        var Fv = F.Id("F");
        var Gv = F.Id("G");
        var z = F.Id("z");
        var s = F.Id("s");
        var n = F.Id("n");
        var C = Seq(Mathbb, Grp(F.Id("C")));
        var fn = (Formula f, Formula x) => Seq(f, Open, x, Close);
        var ratio = (Formula f, Formula x) =>
            new Formula.Fraction(fn(f, Subtract(Multiply(D(2), x), D(1))), fn(f, Multiply(D(2), x)));
        var nonzeroF = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("z"), C,
            NotEqual(fn(Fv, z), D(0)));
        var nonzeroG = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("z"), C,
            NotEqual(fn(Gv, z), D(0)));
        var reading = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("s"), C,
            Equal(ratio(Fv, s), ratio(Gv, s)));
        var shiftQuotient = new Formula.Fraction(fn(Fv, Add(z, n)), fn(Gv, Add(z, n)));
        var shift = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("z"), C)],
            Equal(
                Seq(Lim, Underscore, Grp(n, To, Infty), Sp, shiftQuotient),
                D(1)));
        var hypotheses = new Formula.Logic(nonzeroF, FormulaLogicOperator.And,
            new Formula.Logic(nonzeroG, FormulaLogicOperator.And,
                new Formula.Logic(reading, FormulaLogicOperator.And, shift)));
        return Seq(
            Forall, Sp, Fv, Colon, Sp, C, To, Sp, C, Comma, Sp,
            Forall, Sp, Gv, Colon, Sp, C, To, Sp, C, Comma, Sp,
            hypotheses, Sp, Rightarrow, Sp, Equal(Fv, Gv));
    }
}
