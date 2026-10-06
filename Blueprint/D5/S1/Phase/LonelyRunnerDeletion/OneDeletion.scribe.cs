using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.LonelyRunnerDeletion;

internal sealed class LonelyRunnerDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Phase/LonelyRunnerDeletion/OneDeletion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/zhang2026lonelyrunnerdeletion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zhang's one-deletion Lonely Runner family has the universal 1/N bound and the exact equality cases.",
        H("One-deletion Lonely Runner values"),
        Blocks(Describe.Lean(
            DescribeId.Create("one-deletion-result"),
            DeclarationHandle.Create(Prefix + "result"),
            H("The one-deletion bound and equality classification"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text(
                    "Writing N = n - 1, the speed set is Finset.Icc 1 N with one speed r erased. "
                        + "The Lonely Runner value is the supremum over all real times of the "
                        + "nearest-integer distance. The theorem includes the N = 2 boundary, "
                        + "where either deletion leaves a singleton and equality holds.")),
                Paragraph(Text(
                    "For r > N/2, time 1/r gives a strict surplus over 1/N. For 2r <= N, "
                        + "an explicit q with N+r < q < 2N and an inverse of r modulo q keeps "
                        + "every retained residue at least two units from either endpoint. "
                        + "The endpoint r = N is sharp at time 1/N."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("zhang-2026-lonely-runner-one-deletion"),
                ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var n = F.Id("N");
        var r = F.Id("r");
        var speeds = QualifiedCall(
            "Finset", "erase", QualifiedCall("Finset", "Icc", D(1), n), r);
        var value = Call("lonelyValue", speeds);
        var threshold = new Formula.Fraction(D(1), n);
        var equality = new Formula.Logic(
            Parenthesized(Equal(value, threshold)),
            FormulaLogicOperator.Iff,
            Parenthesized(Or(Equal(r, n), Equal(n, D(2)))));
        var conclusion = And(
            new Formula.Relation(threshold,
                FormulaRelationOperator.LessThanOrEqual, value),
            equality);
        var hypotheses = And(
            new Formula.Relation(D(2),
                FormulaRelationOperator.LessThanOrEqual, n),
            And(
                new Formula.Relation(D(1),
                    FormulaRelationOperator.LessThanOrEqual, r),
                new Formula.Relation(r,
                    FormulaRelationOperator.LessThanOrEqual, n)));
        return Disp(Universal("N", Universal("r", Implies(hypotheses, conclusion))));
    }

    private static Formula Universal(string name, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            Naturals(),
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula QualifiedCall(string module, string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(module), Dot, F.Id(name)), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
