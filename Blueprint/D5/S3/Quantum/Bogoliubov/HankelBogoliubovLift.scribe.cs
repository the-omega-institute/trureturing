using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Bogoliubov;

internal sealed class HankelBogoliubovLiftDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Bogoliubov/HankelBogoliubovLift.hankel_bogoliubov_lift";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite contractive singular-value family has a canonical Bogoliubov lift.",
        H("Hankel Bogoliubov Lift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-contractive-singular-values-have-a-bogoliubov-lift"),
                DeclarationHandle.Create(Declaration),
                H("Finite contractive singular values have a Bogoliubov lift"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite indexed family of Hankel singular values with "
                            + "0 <= sigma_j < 1, define r_j = artanh(sigma_j), "
                            + "alpha_j = cosh(r_j), and beta_j = sinh(r_j).")),
                    Paragraph(Text(
                        "The diagonal coefficient operators satisfy the canonical CCR "
                            + "identity pointwise. The strict interval hypothesis makes the "
                            + "square-root denominator positive and yields the displayed "
                            + "amplitude and particle-number formulas.")),
                    Paragraph(Text(
                        "The pointwise CCR is the finite diagonal form of "
                            + "alpha_H^* alpha_H - beta_H^* beta_H = I; no infinite-dimensional "
                            + "operator is assumed."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Indexed(Formula symbol) =>
        Seq(symbol, Underscore, Grp(F.Id("j")));

    private static Formula Square(Formula value) =>
        new Formula.Power(value, Grp(D(2)));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula sigma = SigmaLower;
        Formula alpha = Indexed(Alpha);
        Formula beta = Indexed(Beta);
        Formula denominator = Call("sqrt", Seq(D(1), Sp, Minus, Sp,
            Square(Indexed(sigma))));
        Formula assumptions = Seq(
            Forall, Sp, F.Id("j"), Sp, InMacro, Sp, Call("Fin", F.Id("n")), Comma, Sp,
            D(0), Sp, Le, Sp, Indexed(sigma), Sp, Land, Sp,
            Indexed(sigma), Sp, Lt, Sp, D(1));

        return Disp(Seq(
            Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            sigma, Sp, InMacro, Sp, Call("Fin", F.Id("n")), F.Id("to"), real, Comma, Sp,
            Grp(assumptions), Sp, Rightarrow, Sp,
            Let(alpha, Call("cosh", Call("artanh", Indexed(sigma)))),
            Let(beta, Call("sinh", Call("artanh", Indexed(sigma)))),
            Grp(
                Forall, Sp, F.Id("j"), Sp, InMacro, Sp, Call("Fin", F.Id("n")), Comma, Sp,
                Square(alpha), Sp, Minus, Sp, Square(beta), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                Forall, Sp, F.Id("j"), Sp, InMacro, Sp, Call("Fin", F.Id("n")), Comma, Sp,
                new Formula.Absolute(alpha), Sp, Eq, Sp, Fraction(D(1), denominator), Sp, Land, Sp,
                Forall, Sp, F.Id("j"), Sp, InMacro, Sp, Call("Fin", F.Id("n")), Comma, Sp,
                new Formula.Absolute(beta), Sp, Eq, Sp,
                Fraction(Indexed(sigma), denominator), Sp, Land, Sp,
                Forall, Sp, F.Id("j"), Sp, InMacro, Sp, Call("Fin", F.Id("n")), Comma, Sp,
                Square(beta), Sp, Eq, Sp,
                Fraction(Square(Indexed(sigma)), Seq(D(1), Sp, Minus, Sp,
                    Square(Indexed(sigma))))), Dot));
    }

    private static Formula Let(Formula name, Formula value) =>
        Seq(Grp(), F.Id("let"), Sp, name, Sp, Eq, Sp, value, Semi);
}
