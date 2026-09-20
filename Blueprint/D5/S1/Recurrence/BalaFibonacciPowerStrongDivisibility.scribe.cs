using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BalaFibonacciPowerStrongDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibonacci minus one at powers of any positive odd base is a strong divisibility sequence.",
        H("Fibonacci Power Strong Divisibility"),
        Blocks(
            Paragraph(Text(
                "Write F for the Fibonacci sequence with F(0)=0 and F(1)=1, "
                + "and a(t)=F(t)-1 for positive t. All indices and the base k are "
                + "natural numbers. Odd k implies k is positive. The gcd is the "
                + "nonnegative greatest common divisor, and subtraction in the "
                + "formal statement is natural subtraction. Every k^r is positive, "
                + "so F(k^r) is at least one and that subtraction agrees with "
                + "integer subtraction. The case k=1 gives zero on both sides.")),
            Describe.Lean(
                DescribeId.Create("bala-strong-divisibility"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/BalaFibonacciPowerStrongDivisibility.result"),
                H("Strong divisibility at odd-base powers"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/bala2022a000071")),
                Blocks(
                    Paragraph(Text(
                        "The statement is the cited conjecture; the following proof "
                        + "is a repository derivation. For a prime p and e>0, work "
                        + "over ZMod(p^e) with Q=[[1,1],[1,0]]. The frozen Lucas "
                        + "recurrence identifies its lower-left entry at power t "
                        + "with F(t). The frozen companion-power shape and determinant "
                        + "give, for odd t and F(t)=1, the matrix [[x+1,1],[1,x]] "
                        + "and x(x+1)=0, where x=F(t+1)-1.")),
                    Paragraph(Text(
                        "Take the natural representative a of x. The prime power "
                        + "divides a(a+1). If p divides a, it does not divide a+1, "
                        + "so coprimality puts the entire prime power in a. Otherwise "
                        + "it goes into a+1. Thus x=0 or x=-1, giving Q^t=Q or "
                        + "Q^t=Q inverse. Conversely, either equality gives F(t)=1 "
                        + "by the lower-left entry. This equivalence includes p=2 "
                        + "and p=5 and uses no division by either prime.")),
                    Paragraph(Text(
                        "On sets of matrix units, let T send a set to its image "
                        + "under g↦g^k and let S={Q,Q inverse}. Mathlib's power "
                        + "iteration and set-image iteration identities show that "
                        + "T iterated r times returns S exactly when Q^(k^r) is "
                        + "Q or Q inverse. The pair argument allows coinciding "
                        + "elements. The preceding equivalence therefore identifies "
                        + "these return times with p^e dividing F(k^r)-1.")),
                    Paragraph(Text(
                        "The existing periodic-point gcd theorem proves the "
                        + "forward divisibility; preservation under multiples "
                        + "proves the reverse one. The prime-power divisibility "
                        + "criterion reconstructs divisibility of natural numbers "
                        + "in both directions. Exponent e=0 contributes only the "
                        + "divisor one. All auxiliary assertions occur inside the "
                        + "single public result and supply no extra formal premise."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a000071-bala-strong-divisibility"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var m = F.Id("m");
        Formula Term(Formula r) => new Formula.Binary(
            Call("F", new Formula.Power(k, r)), FormulaBinaryOperator.Subtract, D(1));
        var conclusion = new Formula.Relation(
            Call("gcd", Term(n), Term(m)), FormulaRelationOperator.Equal,
            Term(Call("gcd", n, m)));
        var assumptions = new Formula.Logic(
            Call("Odd", k), FormulaLogicOperator.And,
            new Formula.Logic(
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n),
                FormulaLogicOperator.And,
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, m)));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("k"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("m"), Naturals()),
            ],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
