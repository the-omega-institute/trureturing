using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class A357512PrimeDivisibilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Oeis =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2022a357512");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fifth-weighted Apery sum at n-1 is divisible by n^4 for every odd n "
            + "not divisible by three, including composite indices.",
        H("A357512: fourth-power divisibility at composite indices"),
        Blocks(
            Paragraph(Text(
                "With offset zero, a(n) sums k^5 choose(n,k)^2 choose(n+k,k)^2 "
                    + "over 0<=k<=n. The theorem proves the conjecture in the "
                    + "OEIS formula section for all n congruent to 1 or 5 modulo 6.")),
            Describe.Lean(
                DescribeId.Create("fourth-power-divisibility"),
                DeclarationHandle.Create("D5/S3/ArithSums/A357512PrimeDivisibility."
                    + "fourth_dvd_of_odd_not_three"),
                H("Divisibility for every admissible natural index"),
                StatementSource.FromAuthor(Divisibility()),
                AssessedProvenance.FromRepo(Oeis),
                Blocks(
                    Paragraph(Text(
                        "Two binomial identities first extract n^2 exactly. Put "
                            + "c(k)=choose(n-1,k)choose(n+k,k). Its recurrence gives "
                            + "(k+1)^2(c(k+1)+c(k))=n^2 c(k), together with an "
                            + "integer witness for n dividing (k+1)(c(k+1)+c(k)).")),
                    Paragraph(Text(
                        "Multiply these identities by c(k+1)-c(k). Modulo n^2, "
                            + "twelve times each remaining summand is the difference "
                            + "of consecutive boundary terms. Summing cancels the "
                            + "interior boundaries; the two endpoints vanish modulo n^2.")),
                    Paragraph(Text(
                        "Since n is odd and three does not divide n, twelve is "
                            + "coprime to n^2 and can be cancelled. The exact initial "
                            + "factor supplies the other n^2. No summation index is "
                            + "inverted, so the proof applies to composite n."))),
                DescribeRole.Theorem))));

    private static Formula Divisibility()
    {
        Formula n = F.Id("n");
        Formula odd = new Formula.Apply(F.Id("Odd"), [n]);
        Formula notThree = F.Seq(F.Neg, F.Grp(
            new Formula.Relation(F.D(3), FormulaRelationOperator.Divides, n)));
        Formula previous = new Formula.Binary(n, FormulaBinaryOperator.Subtract, F.D(1));
        Formula conclusion = new Formula.Relation(F.Seq(n, F.Caret, F.Grp(F.D(4))),
            FormulaRelationOperator.Divides, new Formula.Apply(F.Id("a"), [previous]));
        Formula hypotheses = new Formula.Logic(odd, FormulaLogicOperator.And, notThree);
        return F.Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), F.Seq(F.Mathbb, F.Grp(F.Id("N"))),
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }
}
