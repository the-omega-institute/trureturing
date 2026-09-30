using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class Erdos375ThreeCompositesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/Erdos375ThreeComposites.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three consecutive composite integers admit pairwise distinct prime divisors.",
        H("Erdős #375: three consecutive composites"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos375-three-distinct-prime-divisors"),
                DeclarationHandle.Create(
                    Prefix + "exists_distinct_prime_divisors_of_three_composites"),
                H("Distinct prime divisors for three consecutive composites"),
                StatementSource.FromAuthor(ThreeCompositeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For n at least one, assume n+1, n+2 and n+3 are all composite. "
                            + "The theorem supplies prime divisors p1, p2 and p3 of the "
                            + "corresponding terms and proves all three pairwise inequalities.")),
                    Paragraph(Text(
                        "The endpoint argument uses the four-divisibility alternative: both "
                            + "endpoints cannot be multiples of four because their difference "
                            + "is two, so one endpoint has an odd prime divisor. Coprimality of "
                            + "successive terms separates the middle divisor. This is only the "
                            + "three-term slice of the open Grimm conjecture; no claim for "
                            + "intervals of length at least four is made."))),
                DescribeRole.Theorem))));

    private static Formula ThreeCompositeFormula()
    {
        Formula n = V("n");
        Formula p1 = V("p1");
        Formula p2 = V("p2");
        Formula p3 = V("p3");
        Formula assumptions = And(
            Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n),
            Not(Call("Prime", Add(n, D(1)))),
            Not(Call("Prime", Add(n, D(2)))),
            Not(Call("Prime", Add(n, D(3)))));
        Formula conclusion = And(
            Call("Prime", p1),
            Call("Prime", p2),
            Call("Prime", p3),
            Divides(p1, Add(n, D(1))),
            Divides(p2, Add(n, D(2))),
            Divides(p3, Add(n, D(3))),
            NotEqual(p1, p2),
            NotEqual(p1, p3),
            NotEqual(p2, p3));
        Formula existential = Seq(
            Exists, Sp, p1, Comma, Sp, p2, Comma, Sp, p3, Sp, InMacro,
            Sp, Naturals(), Comma, Sp, conclusion);
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Implies(assumptions, existential), Dot));
    }

    private static Formula V(string name) => F.Id(name);

    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula item in rest)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, item);
        }

        return result;
    }

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Not(Formula value) =>
        new Formula.Not(value);

    private static Formula Relation(
        Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Divides, right);
}
