using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class NymanBeurlingShellMassDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/NymanBeurlingShellMassDecomposition."
            + "nyman_beurling_shell_mass_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal shell tails satisfy the exact mass recurrence and detect the terminal defect.",
        H("Nyman-Beurling Shell Mass Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("nyman-beurling-shell-mass-decomposition"),
            DeclarationHandle.Create(Declaration),
            H("Shell recurrence, terminal mass, and RH"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a unit target have a complete orthogonal Hilbert-sum decomposition "
                        + "into a zero initial component, extracted shells, and a terminal "
                        + "component. Identify the terminal component with the orthogonal "
                        + "Nyman-Beurling defect.")),
                Paragraph(Text(
                    "Writing shell n for source coordinate Q_(n+1), the squared tail distance "
                        + "is the sum of all later shell masses and the terminal mass. Consecutive "
                        + "tails differ by exactly one shell, and total mass is one.")),
                Paragraph(Text(
                    "The source omitted the definitions and compatibility assumptions connecting "
                        + "the shell projections, distances, terminal projection, and RH. The Lean "
                        + "statement makes those hypotheses explicit and uses the analytic "
                        + "Nyman-Beurling criterion as an assumption."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EqualFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("N");
        Formula dN = Call("d", n);
        Formula dNext = Call("d", Seq(n, Plus, D(1)));
        Formula shell = Call("shellMass", n);
        Formula terminal = Call("terminalMass");
        Formula recurrence = EqualFormula(
            new Formula.Power(dN, D(2)),
            Seq(new Formula.Power(dNext, D(2)), Plus, shell));
        Formula tail = EqualFormula(
            new Formula.Power(dN, D(2)),
            Seq(Call("tailShellMass", n), Plus, terminal));
        Formula total = EqualFormula(
            Seq(Call("totalShellMass"), Plus, terminal),
            D(1));
        Formula rhTerminal = Iff(F.Id("RH"), EqualFormula(terminal, D(0)));
        Formula rhShells = Iff(
            F.Id("RH"),
            EqualFormula(Call("totalShellMass"), D(1)));

        return Disp(And(
            Call("forallNat", n, recurrence),
            And(Call("forallNat", n, tail), And(total, And(rhTerminal, rhShells)))));
    }
}
