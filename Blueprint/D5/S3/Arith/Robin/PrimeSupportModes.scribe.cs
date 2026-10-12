using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimeSupportModesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every natural number belongs to one of five distinct-prime support strata, and the two-through-eight stratum is already covered by the Robin theorem.",
        H("Five Prime-Support Modes for the Robin Reduction"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-support-modes"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PrimeSupportModes.primeSupportMode_cases"),
            H("Exhaustive support classification"),
            StatementSource.FromAuthor(ClassificationFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The five bins are empty support, singleton support, two through eight distinct primes, "
                        + "nine through eleven distinct primes, and at least twelve distinct primes.")),
                Paragraph(Text(
                    "The two-through-eight bin reuses the existing formal Robin theorem above 5040. "
                        + "The remaining bins stay explicit interfaces for the Euler-layer and clock arguments; "
                        + "a strict failure above 5040 is therefore forced into the nine-through-eleven "
                        + "or twelve-plus bin. This document does not claim the full Robin theorem."))),
            DescribeRole.Theorem))));

    private static Formula ClassificationFormula()
    {
        Formula c = Call("card", Call("primeFactors", F.Id("n")));
        Formula disjunction = new Formula.Logic(
            Eq(c, Num(0)), FormulaLogicOperator.Or,
            new Formula.Logic(
                Eq(c, Num(1)), FormulaLogicOperator.Or,
                new Formula.Logic(
                    And(Le(Num(2), c), Le(c, Num(8))), FormulaLogicOperator.Or,
                    new Formula.Logic(
                        And(Le(Num(9), c), Le(c, Num(11))), FormulaLogicOperator.Or,
                        Le(Num(12), c)))));
        return Disp(All("n", disjunction));
    }

    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
        Seq(Mathbb, Grp(F.Id("N"))), body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
