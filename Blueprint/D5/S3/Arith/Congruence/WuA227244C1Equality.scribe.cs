using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class WuA227244C1EqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least prime divisor on this entire arithmetic progression is 101.",
        H("Wu's A227244 Conjecture 1"),
        Blocks(Describe.Lean(
            DescribeId.Create("a227244-c1-equality"),
            DeclarationHandle.Create("D5/S3/Arith/Congruence/WuA227244C1Equality.result"),
            H("The full equality for every natural index"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Arith/wu2026a227244")),
            Blocks(Paragraph(Text("For every natural n, including zero, the integer with index 20*n+16 is divisible by the prime 101, and every natural prime divisor is at least 101. The product and subtraction are in the integers and every exponent is natural. Periodicity reduces the modular powers to finite residue tables; the reduction identities apply at every natural index. The tables prove divisibility by 101 and exclude each smaller prime. Thus the finite certificates establish the entire unbounded equality, without an exclusion or an upper bound on n."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a227244-c1-equality"), ResolutionKind.Proved)))));

    private static Formula Statement()
    {
        Formula n = F.Id("n");
        Formula q = F.Id("q");
        Formula index = Seq(D(2,0), Star, n, Plus, D(1,6));
        Formula value = Seq(Open, Power(Cast(D(2)), Power(D(2), index)), Plus, D(1), Close,
            Star, Power(Cast(D(2)), Power(D(2), Power(D(2), index))), Minus, D(1));
        return All("n", And(Call("Prime", D(1,0,1)), And(Divides(Cast(D(1,0,1)), value),
            All("q", Implies(Call("Prime", q), Implies(Divides(Cast(q), value),
                new Formula.Relation(D(1,0,1), FormulaRelationOperator.LessThanOrEqual, q)))))));
    }
    private static Formula Cast(Formula value) => Seq(Open, value, Colon, Sp, Mathbb, Grp(F.Id("Z")), Close);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("N"))))], body);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, Par(right));
}
