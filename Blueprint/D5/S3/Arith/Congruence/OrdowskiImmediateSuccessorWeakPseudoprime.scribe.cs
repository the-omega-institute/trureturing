using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class OrdowskiImmediateSuccessorWeakPseudoprimeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/OrdowskiImmediateSuccessorWeakPseudoprime.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/ferreol2018a239293");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordowski's immediate-successor weak-pseudoprime condition holds exactly at odd composite successors.",
        H("Ordowski's Immediate-Successor Weak Pseudoprime Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a239293-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Odd composite successors are exactly the qualifying successors"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least one, the composite successor n+1 satisfies "
                        + "the weak-pseudoprime congruence exactly when n+1 is odd. Since n+1 "
                        + "is the immediate successor of n, qualification at this modulus is "
                        + "already least among qualifying composites greater than n. Modulo "
                        + "n+1, the residue of n is minus one, so its power is classified by "
                        + "the parity of n+1. An even qualifying successor would make minus "
                        + "one equal to one; compositeness excludes the only boundary modulus "
                        + "two. The underlying casts, parity powers, and residue facts are "
                        + "pinned Mathlib material."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a239293-ordowski-immediate-successor-weak-pseudoprime"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var successor = Add(n, D(1));
        var modularEquality = Equal(
            new Formula.Modulo(Power(n, successor), successor),
            new Formula.Modulo(n, successor));
        var qualifying = And(
            Less(D(1), successor),
            And(NotPrime(successor), modularEquality));
        var oddComposite = And(
            NotPrime(successor),
            And(Call("Odd", successor), Less(D(1), successor)));
        var characterization = Iff(
            Parenthesized(qualifying),
            Parenthesized(oddComposite));
        return Disp(Universal("n", Implies(
            LessOrEqual(D(1), n),
            Parenthesized(characterization))));
    }

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula NotPrime(Formula value) =>
        new Formula.Not(Call("Prime", value));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
