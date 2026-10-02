using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class KimberlingLeastTwoSubsetCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/kimberling2022a077866");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least-two-element subset count agrees with OEIS A077866 after shifting the index by three.",
        H("Kimberling's least-two-element subset count"),
        Blocks(
            Paragraph(Text("For a subset of {1,...,N}, let b(N) count those with two least "
                + "elements a<b and maximum a+b. Positivity makes the source's "
                + "more-than-one-element condition automatic. The sequence A is defined "
                + "independently by A(0)=1, A(1)=2, A(2)=5, A(3)=8 and "
                + "A(n+4)+4 A(n+1)=2 A(n+3)+A(n+2)+2 A(n).")),
            Describe.Lean(
                DescribeId.Create("kimberling-least-two-subset-count-result"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/KimberlingLeastTwoSubsetCount.result"),
                H("All-index subset interpretation of A077866"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every counted subset uniquely has the form "
                    + "{a,b,a+b} union T, where 0<a<b, a+b<=N, and T is any subset "
                    + "of (b,a+b). The resulting weighted sum is evaluated at odd "
                    + "and even indices and matched to the independently defined "
                    + "OEIS recurrence. The three empty-range base cases are explicit."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a077866-least-two-subset-count"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        Formula b = F.Id("b");
        Formula a = F.Id("A");
        Formula n = F.Id("n");
        Formula zero = F.D(0);
        Formula initial = And(Eq(App(b, zero), zero),
            And(Eq(App(b, F.D(1)), zero), Eq(App(b, F.D(2)), zero)));
        Formula shifted = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), F.Seq(F.Mathbb, F.Grp(F.Id("N"))),
            Eq(App(b, Add(n, F.D(3))), App(a, n)));
        return F.Disp(And(initial, shifted));
    }

    private static Formula App(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
}
