using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BalaLucasFiveAdicCongruenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/BalaLucasFiveAdicCongruence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala's quintic recurrence satisfies the conjectured power-of-five congruence.",
        H("Bala's Lucas Five-Adic Congruence"),
        Blocks(
            Paragraph(Text(
                "The symbol ℕ denotes the natural numbers including zero, and ℤ "
                    + "denotes the integers. The sequence a maps ℕ to ℤ; n and r "
                    + "are natural indices, and r≤n is their usual order relation. "
                    + "The symbol ∣ denotes integer divisibility; addition, "
                    + "subtraction, multiplication, and powers of sequence values "
                    + "are in ℤ, with natural exponents. Index arithmetic is in ℕ. "
                    + "Lucas denotes the Lucas sequence. "
                    + "The seed a(0)=1=Lucas(5^0) gives a(1)=11=A144837(1), "
                    + "agreeing with the OEIS offset 1. Only the Conjecture line "
                    + "in Peter Bala's Nov 14 2022 block is settled, for all n "
                    + "and r≤n, covering n≥1 and also n=0. The Lucas representation, "
                    + "the 5-adic limit (A269591), and A268922 are not claimed.")),
            Describe.Lean(
                DescribeId.Create("a144837-a"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The integer quintic recurrence"),
                StatementSource.FromAuthor(SequenceFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/bala2022a144837")),
                Blocks(Paragraph(Text(
                    "The initial value is 1. Each next term is the sum of the "
                        + "current term's fifth power, five times its cube, and "
                        + "five times the term. This is Bala's recurrence extended "
                        + "to index zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a144837-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The growing-modulus congruence"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/bala2022a144837")),
                Blocks(Paragraph(Text(
                    "Induction gives 5^(2n+1) ∣ a(n)^2+4. The initial square "
                        + "plus 4 is 5, and a(n+1)^2+4 equals "
                        + "(a(n)^4+3a(n)^2+1)^2(a(n)^2+4). The identity "
                        + "a(n)^4+3a(n)^2+1=(a(n)^2+4)(a(n)^2-1)+5 "
                        + "makes the squared factor divisible by 25. Thus each "
                        + "step gains two powers of 5. The difference factors as "
                        + "a(n+1)-a(n)=a(n)(a(n)^2+1)(a(n)^2+4). Finally, "
                        + "r≤n gives n+r+1≤2n+1 and the stated divisor."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a144837-bala-lucas-five-adic-congruence"),
                    ResolutionKind.Proved)))));

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        return Disp(new Formula.Aligned([
            Seq(Operatorname, Grp(F.Id("a")), Colon, Sp,
                Naturals(), Sp, To, Sp, Integers()),
            new Formula.Relation(Call("a", D(0)), FormulaRelationOperator.Equal, D(1)),
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals())],
                new Formula.Relation(
                    Call("a", Add(n, D(1))), FormulaRelationOperator.Equal,
                    Add(
                        Add(new Formula.Power(Call("a", n), D(5)),
                            new Formula.Binary(
                                D(5), FormulaBinaryOperator.Multiply,
                                new Formula.Power(Call("a", n), D(3)))),
                        new Formula.Binary(D(5), FormulaBinaryOperator.Multiply, Call("a", n))))),
        ]));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var r = F.Id("r");
        var hypothesis = new Formula.Relation(r, FormulaRelationOperator.LessThanOrEqual, n);
        var conclusion = new Formula.Relation(
            new Formula.Power(
                Parenthesized(Seq(D(5), Colon, Sp, Integers())), Add(Add(n, r), D(1))),
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
