using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class DisjointPhysicalBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical budget when the deficits exceed the dimension",
        H("The physical budget when the deficits exceed the dimension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("excess-deficits-disjoint"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/DisjointPhysicalBudget.excess_deficits_disjoint"),
                H("The capacity reduction to two small effects"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If the ambient capacity is at least twice the working dimension d and the deficits Σ_j (d − m_j)₊ exceed d, one label has capacity at least d and the other two capacities sum to less than d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sharp-record-budget-of-excess-deficits"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/DisjointPhysicalBudget.sharp_record_budget_of_excess_deficits"),
                H("Attainment under the original record law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At an admissible rank and feasible law, use the smaller of rank and corank, with the direct branch at a tie. If the deficits exceed the working dimension, the disjoint formula gives a valid certificate and an attained physical budget through the exact gain range. The coherent record retains the original law."))),
                DescribeRole.Theorem))));
}
