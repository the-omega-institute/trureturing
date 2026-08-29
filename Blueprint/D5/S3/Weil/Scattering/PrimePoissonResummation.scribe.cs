using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class PrimePoissonResummationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted bilateral translation history of one prime is the centered unitary "
            + "Poisson resolvent without a remainder.",
        H("Prime Poisson Resummation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-history-is-the-centered-poisson-resolvent"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Scattering/PrimePoissonResummation."
                        + "prime_poisson_resummation"),
                H("Prime-power translation histories resum exactly"),
                StatementSource.FromAuthor(Disp(Formula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p, the radius is one over square root p and the unitary "
                            + "is real-line L2 translation by log p. Both constructions are "
                            + "displayed in the statement.")),
                    Paragraph(Text(
                        "The left side is the complete positive-index bilateral orbit series. "
                            + "The right side uses the independently resolvent-defined Poisson "
                            + "operator, so the equality records the local Neumann bridge rather "
                            + "than installing the series by definition."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        var p = F.Id("p");
        var psi = F.Id("psi");
        var n = F.Id("n");
        var r = F.Id("r");
        var unitary = F.Id("U");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var ltwo = Call("Ltwo", reals, complex);
        var successor = Seq(n, Sp, Plus, Sp, D(1));
        var radiusPower = new Formula.Power(Seq(r), successor);
        var forwardPower = new Formula.Power(Seq(unitary), successor);
        var adjointPower = new Formula.Power(Call("adjoint", unitary), successor);
        var forwardCorrelation = Call("inner", psi, Call("apply", forwardPower, psi));
        var backwardCorrelation = Call("inner", psi, Call("apply", adjointPower, psi));
        var series = Seq(
            Sum, Underscore, Grp(n, Eq, D(0)), Caret, Grp(Infty), Sp,
            radiusPower, Sp, Times, Sp,
            OpenBracket, Add(forwardCorrelation, backwardCorrelation), CloseBracket);
        var logWeight = Seq(Minus, Call("log", p));
        var centered = Subtract(Call("unitaryPoissonOperator", r, unitary),
            Call("identity"));
        var rightInner = Call("inner", psi, Call("apply", centered, psi));
        var equality = Equal(
            Seq(logWeight, Sp, Times, Sp, series),
            Seq(logWeight, Sp, Times, Sp, rightInner));
        var radiusDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            r, Colon, Sp, reals, Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(Call("sqrt", p)), Semi, Sp);
        var unitaryDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            unitary, Colon, Sp, new Formula.TypeArrow(ltwo, ltwo), Sp, Eq, Sp,
            Call("realTranslation", Call("log", p)), Semi, Sp);
        var body = Seq(radiusDefinition, unitaryDefinition, equality);

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("p"), naturals),
             new Formula.BoundVariable(FormulaIdentifier.Create("psi"), ltwo)],
            new Formula.Logic(
                Call("Prime", p),
                FormulaLogicOperator.Implies,
                body));
    }
}
