using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution.AxisBudgets;

internal sealed class AxisCoordinateRelabelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transfer a single-coordinate budget by permuting the coordinates.",
        H("Relabeling the marked coordinate"),
        Blocks(Describe.Lean(
            DescribeId.Create("axis-feasibility-invariant-under-relabeling"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/AxisBudgets/CoordinateRelabel.axis_feasibility_iff"),
            H("Every marked coordinate has the same feasible budgets"),
            StatementSource.FromAuthor(Disp(new Formula.Logic(
                Call("AxisFactorWithin", F.Id("k"), F.Id("i"), F.Id("b")),
                FormulaLogicOperator.Iff,
                Call("AxisFactorWithin", F.Id("k"), F.Id("j"), F.Id("b"))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For any dimension d, take marked coordinates i and j in Fin d, "
                    + "a natural multiplier k and a natural budget b. AxisFactorWithin is the "
                    + "one-coordinate Boolean inclusion factor predicate at that multiplier and budget.")),
                Paragraph(Text("Apply the transposition of i and j to the elements of each row "
                    + "and column subset. Inclusion, subset sizes and the full-set pivot are preserved. "
                    + "Transport each entry along these bijections. Each row and column keeps its "
                    + "degree and the exceptional loop remains absent. The charge is unchanged "
                    + "because it counts edges between the same odd ranks away from the full row."))),
            DescribeRole.Theorem))));
}
