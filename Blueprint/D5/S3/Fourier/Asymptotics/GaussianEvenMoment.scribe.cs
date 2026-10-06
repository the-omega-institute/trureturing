using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class GaussianEvenMomentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The central even moments of a real Gaussian law are exact at every nonnegative variance.",
        H("Scalar Gaussian even moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("gaussian-central-even-moment"),
            DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/GaussianEvenMoment.centralMoment_two_mul"),
            H("Exact moments including zero variance"),
            StatementSource.FromAuthor(MomentFormula()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
            Blocks(
                Paragraph(Text("For a real mean mu, nonnegative standard deviation sigma and natural n, the central moment of order 2n of N(mu,sigma^2) equals sigma^(2n) times (2n-1) double factorial. At n=0 the natural subtraction is truncated and the double factorial is one. The formula includes sigma=0.")),
                Paragraph(Text("Translation removes the mean. The centered Gaussian density is even, so the integral reduces to the positive half-line. The substitution x=sigma sqrt(2u) gives a Gamma integral at n+1/2, whose half-integer value supplies the double factorial. The second and fourth moments are sigma^2 and 3 sigma^4.")),
                Paragraph(Text("Its standard-normal specialization supplies the even moments used in the countable centered Gaussian quadratic-series theorem."))),
            DescribeRole.Theorem))));

    private static Formula MomentFormula()
    {
        Formula mu = F.Id("mu"), sigma = F.Id("sigma"), n = F.Id("n"),
            twice = Multiply(F.D(2), n);
        Formula lhs = Call("centralMoment", F.Id("id"), twice,
            Call("gaussianReal", mu, new Formula.Power(sigma, F.D(2))));
        Formula rhs = Multiply(new Formula.Power(sigma, twice),
            new Formula.Apply(F.Seq(F.Id("Nat"), F.Dot, F.Id("doubleFactorial")),
                [F.Grp(F.Seq(twice, F.Minus, F.D(1)))]));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("mu"), F.Id("Real")),
             new Formula.BoundVariable(FormulaIdentifier.Create("sigma"), F.Id("NNReal")),
             new Formula.BoundVariable(FormulaIdentifier.Create("n"), F.Id("Nat"))],
            new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs)));
    }
}
