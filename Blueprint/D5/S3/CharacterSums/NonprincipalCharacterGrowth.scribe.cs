using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class NonprincipalCharacterGrowthDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/NonprincipalCharacterGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-totient growth of a nonprincipal Dirichlet L-function",
        H("Cancellation within one period"),
        Blocks(
            Paragraph(Text("For a complex nonprincipal character of positive modulus q, each full "
                + "period sums to zero. Its total absolute mass is the number of units modulo q. "
                + "An incomplete period and its complement have opposite sums, so the norm of "
                + "either sum is at most half that mass.")),
            Describe.Lean(DescribeId.Create("right-half-plane"), DeclarationHandle.Create(Module + "nonprincipal_growth"),
                H("Growth throughout the right half-plane"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Take any complex s with σ = Re(s) > 0. Write A(t) for the character "
                        + "sum over positive integers up to t. Partial summation on σ > 1 identifies "
                        + "L(s,χ) with s times the integral of A(t)t to the power −s−1 from one to infinity. "
                        + "Boundedness of A makes its Mellin integral holomorphic throughout σ > 0, "
                        + "so analytic continuation extends the identity to this half-plane.")),
                    Paragraph(Text("The absolute value of the remaining power integrates to 1/σ. "
                        + "Multiplying by |s| and the incomplete-period bound φ(q)/2 gives the stated estimate.")),
                    Paragraph(Text("The positive modulus is part of the definition of this L-function. "
                        + "For the principal character modulo three at s = 2 the first and second terms "
                        + "already give 1 + 1/4, and every later term is nonnegative. The displayed "
                        + "allowance is 1. For the nonprincipal character modulo three at s = −1 the "
                        + "allowance is −1, below every norm."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula q = F.Id("q"), chi = F.Id("chi"), s = F.Id("s");
        Formula re = Call("Re", s);
        Formula hypotheses = new Formula.Logic(
            new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, q), FormulaLogicOperator.And,
            new Formula.Logic(new Formula.Relation(chi, FormulaRelationOperator.NotEqual, F.D(1)),
                FormulaLogicOperator.And, new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, re)));
        Formula upper = F.Seq(Call("phi", q), F.Sp, Call("abs", s), F.Slash,
            F.Open, F.D(2), F.Sp, re, F.Close);
        Formula conclusion = new Formula.Relation(Call("abs", Call("L", s, chi)),
            FormulaRelationOperator.LessThanOrEqual, upper);
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("q"), F.Id("Nat")),
             new(FormulaIdentifier.Create("chi"), Call("DirichletCharacter", F.Id("Complex"), q)),
             new(FormulaIdentifier.Create("s"), F.Id("Complex"))],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
