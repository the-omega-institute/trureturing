using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathAggregateBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite certificate families carry a uniform quadratic ray-distance budget, a compatible quartic budget, and the numerical square-root budget used by the padded Kraus comparison.",
        H("Four-path aggregate stability budgets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-path-certificate-distance-budget"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathAggregateBudget.certificate_distance_budget"),
                H("Certificate distance budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A pointwise certificate gap bounded by 1600 times the coordinatewise minimum sums to the same bound for the finite family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-path-quartic-distance-budget"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathAggregateBudget.quartic_distance_budget"),
                H("Quartic distance budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under complete coordinate totals, every minimum lies in the unit interval, so its square inherits the quadratic certificate budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-path-square-root-budget"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathAggregateBudget.square_root_budget"),
                H("Square-root budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The column estimate, certificate budget, and actual trace-defect identity propagate to the constant 480 times square root of 2 times square root of epsilon."))),
                DescribeRole.Theorem))));
}
