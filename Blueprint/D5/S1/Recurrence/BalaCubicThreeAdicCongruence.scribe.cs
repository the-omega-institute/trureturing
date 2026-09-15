using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BalaCubicThreeAdicCongruenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/BalaCubicThreeAdicCongruence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala's cubic recurrence satisfies the conjectured power-of-three congruence.",
        H("Bala's Cubic Three-Adic Congruence"),
        Blocks(
            Paragraph(Text(
                "The sequence a maps the natural numbers to the integers; n and r "
                    + "are natural indices. The symbol ∣ denotes divisibility in ℤ, "
                    + "so the modulus and the sequence difference are integers. "
                    + "Powers have natural exponents. Only the Conjecture line in "
                    + "Peter Bala's Nov 15 2022 block for A002000 is settled here, "
                    + "for every n and every r<=n. The Lucas representation, "
                    + "the 3-adic limit, and the product formula are not claimed. "
                    + "The sequence is defined by the NAME recurrence.")),
            Describe.Lean(
                DescribeId.Create("a002000-a"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The integer cubic recurrence"),
                StatementSource.FromAuthor(SequenceFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/bala2022a002000")),
                Blocks(Paragraph(Text(
                    "The initial value is 7. Each next term is the current term "
                        + "multiplied by its square minus 3. Both subtraction and "
                        + "multiplication take place in the integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a002000-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The growing-modulus congruence"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/bala2022a002000")),
                Blocks(Paragraph(Text(
                    "Induction gives 3^(2n+2) ∣ a(n)+2. The initial value plus 2 "
                        + "is 9, and a(n+1)+2=(a(n)-1)^2(a(n)+2). Since 3 divides "
                        + "a(n)+2, it also divides a(n)-1, supplying two further "
                        + "powers of 3 at each step. The difference factors as "
                        + "a(n+1)-a(n)=a(n)(a(n)-2)(a(n)+2). Finally, r<=n gives "
                        + "n+r+2<=2n+2, so the desired power divides the difference."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a002000-bala-cubic-three-adic-congruence"),
                    ResolutionKind.Proved)))));

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        return Disp(new Formula.Aligned([
            Seq(Operatorname, Grp(F.Id("a")), Colon, Sp,
                Naturals(), Sp, To, Sp, Integers()),
            new Formula.Relation(Call("a", D(0)), FormulaRelationOperator.Equal, D(7)),
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals())],
                new Formula.Relation(
                    Call("a", Add(n, D(1))), FormulaRelationOperator.Equal,
                    new Formula.Binary(
                        Call("a", n), FormulaBinaryOperator.Multiply,
                        Parenthesized(Subtract(new Formula.Power(Call("a", n), D(2)), D(3)))))),
        ]));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var r = F.Id("r");
        var hypothesis = new Formula.Relation(r, FormulaRelationOperator.LessThanOrEqual, n);
        var conclusion = new Formula.Relation(
            new Formula.Power(
                Parenthesized(Seq(D(3), Colon, Sp, Integers())), Add(Add(n, r), D(2))),
            FormulaRelationOperator.Divides,
            Subtract(Call("a", Add(n, D(1))), Call("a", n)));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("r"), Naturals()),
            ],
            new Formula.Logic(
                Parenthesized(hypothesis), FormulaLogicOperator.Implies,
                Parenthesized(conclusion))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
