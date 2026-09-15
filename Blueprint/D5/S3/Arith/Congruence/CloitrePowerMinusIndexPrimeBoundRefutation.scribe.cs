using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class CloitrePowerMinusIndexPrimeBoundRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/cloitre2002a072872");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The n = 6298 certificate refutes Cloitre's A072872 prime-index upper bound.",
        H("The OEIS A072872 Prime-Index Upper-Bound Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a072872-sequence"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The least positive power-minus-index witness"),
                StatementSource.FromAuthor(AFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each natural n, a(n) is the least positive k for which n divides "
                        + "2^k - k. The natural-number convention gives sInf of an empty "
                        + "set the value zero; no general existence assertion is made."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a072872-prime-index-upper-bound"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Cloitre's prime-index upper-bound conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural n greater than 47, the conjecture says that a(n) "
                        + "is less than the n-th prime, with the source's prime(n) notation "
                        + "represented by Nat.nth Nat.Prime (n - 1)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a072872-prime-index-upper-bound-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture fails at n = 6298"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The modular certificate proves a(6298) = 77742, while the prime-count "
                        + "certificate proves that the 6298th prime is 62753. Hence the "
                        + "universal upper bound is false."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a072872-power-minus-index-prime-bound-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula AFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var condition = new Formula.Logic(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, k),
            FormulaLogicOperator.And,
            new Formula.Relation(
                n,
                FormulaRelationOperator.Divides,
                new Formula.Binary(
                    new Formula.Power(D(2), k),
                    FormulaBinaryOperator.Subtract,
                    k)));
        var witnesses = Seq(
            OpenBrace, k, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            Parenthesized(condition), CloseBrace);
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            new Formula.Relation(
                Call("a", n),
                FormulaRelationOperator.Equal,
                Call("sInf", witnesses))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var body = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            new Formula.Logic(
                new Formula.Relation(Num(47), FormulaRelationOperator.LessThan, n),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    Call("a", n),
                    FormulaRelationOperator.LessThan,
                    Call("nth", F.Id("Prime"),
                        new Formula.Binary(n, FormulaBinaryOperator.Subtract, D(1))))));
        return Disp(new Formula.Logic(
            Parenthesized(F.Id("claim")),
            FormulaLogicOperator.Iff,
            Parenthesized(body)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
