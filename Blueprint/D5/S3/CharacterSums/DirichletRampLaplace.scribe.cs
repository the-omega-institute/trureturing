using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletRampLaplaceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/DirichletRampLaplace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Laplace transforms of character-weighted Mangoldt ramps",
        H("Laplace transforms on the line of real part two"),
        Blocks(
            Paragraph(Text("For a complex Dirichlet character χ of positive modulus, the character ramp "
                + "weights each von Mangoldt ramp by χ(n). The transform is taken in the coordinate "
                + "y = log x over y > 0, with s(t) = 2 + 2πit for any real frequency t. "
                + "Here L denotes the Dirichlet L-function and L′ its complex derivative in the first variable.")),
            Describe.Lean(DescribeId.Create("character-ramp-transform"),
                DeclarationHandle.Create(Module + "characterRamp_line_laplace"),
                H("The twisted transform for every character"),
                StatementSource.FromAuthor(Statement(centered: false)), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At fixed y the ramp terms are supported on positive integers at most exp y. "
                        + "The character norm is at most one, so the summable integrals of the unweighted ramp norms "
                        + "dominate the twisted ones. This gives absolute sum–integral interchange. The individual "
                        + "ramp transforms give the twisted von Mangoldt series divided by s(s − 1). The Dirichlet "
                        + "series for the negative logarithmic derivative identifies its sum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("centered-ramp-transform"),
                DeclarationHandle.Create(Module + "gChi_line_laplace"),
                H("The centered transform for a nonprincipal character"),
                StatementSource.FromAuthor(Statement(centered: true)), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For nonprincipal χ the centered ramp adds x times L′(1,χ)/L(1,χ) to the "
                        + "character ramp. The character ramp times the transform kernel is integrable by domination "
                        + "by the complete Mangoldt ramp. The added term is an integrable exponential with exponent "
                        + "(1 − s)y. Integrating it adds L′(1,χ)/L(1,χ) divided by s − 1."))),
                DescribeRole.Theorem))));

    private static Formula Statement(bool centered)
    {
        Formula modulus = F.Id("N"), chi = F.Id("chi"), t = F.Id("t"), y = F.Id("y");
        Formula s = new Formula.Apply(F.Id("s"), [t]);
        Formula sMinusOne = F.Seq(s, F.Minus, F.D(1));
        Formula exponential = new Formula.Apply(F.Exp, [y]);
        Formula kernel = new Formula.Apply(F.Exp, [F.Seq(F.Minus, s, F.Sp, y)]);
        Formula ramp = Call(centered ? "gChi" : "characterRamp", chi, exponential);
        Formula integral = F.Seq(F.Int, F.Underscore, F.Grp(y, F.Gt, F.D(0)),
            F.Sp, kernel, F.Sp, ramp, F.Thin, F.Id("d"), y);

        Formula transform = Fraction(
            F.Seq(F.Minus, LogDerivative(s, chi)), F.Seq(s, F.Open, sMinusOne, F.Close));
        if (centered)
            transform = F.Seq(transform, F.Plus, Fraction(LogDerivative(F.D(1), chi), sMinusOne));

        Formula hypotheses = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, modulus);
        if (centered)
            hypotheses = new Formula.Logic(hypotheses, FormulaLogicOperator.And,
                new Formula.Relation(chi, FormulaRelationOperator.NotEqual, F.D(1)));

        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("N"), F.Seq(F.Mathbb, F.Grp(F.Id("N")))),
             new(FormulaIdentifier.Create("chi"),
                 Call("DirichletCharacter", F.Seq(F.Mathbb, F.Grp(F.Id("C"))), modulus)),
             new(FormulaIdentifier.Create("t"), F.Seq(F.Mathbb, F.Grp(F.Id("R"))))],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies,
                new Formula.Relation(integral, FormulaRelationOperator.Equal, transform))));
    }

    private static Formula LogDerivative(Formula argument, Formula chi) =>
        Fraction(new Formula.Apply(F.Seq(F.Id("L"), F.Apos), [argument, chi]),
            new Formula.Apply(F.Id("L"), [argument, chi]));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
