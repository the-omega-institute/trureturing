using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class ExactPartitionCountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit ExactPartitionCounting constructions. The linked declarations do not certify unproved analytic or quantum extensions.",
        H("ExactPartitionCounting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-cnf-counting-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ExactPartitionCounting.exact_cnf_counting_recovery"),
                H("exact cnf counting recovery"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input is a CNF syntax tree. Assignments, clause evaluation, violations, the rational Gibbs partition, and the extra visible bit are constructed. Taking the floor after multiplying the total partition by two thirds returns the satisfying-assignment count."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clause-three-local"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ExactPartitionCounting.clause_three_local"),
                H("clause three local"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A clause of length at most three depends only on its explicit support, whose cardinality is at most three. Repeated literals and empty clauses are allowed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clauseprojector-idempotent"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjector_idempotent"),
                H("clauseProjector idempotent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal 0/1 violation operator is a projection in the rational matrix algebra."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clauseprojectors-commute"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjectors_commute"),
                H("clauseProjectors commute"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicitly defined clause projections commute; no commutativity certificate is assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-denominator"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ExactPartitionCounting.common_denominator"),
                H("common denominator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication by two to the power (n+1) times the clause count yields the explicitly constructed natural numerator. This is an exact encoding identity, not a running-time or approximation-hardness theorem."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boltzmann-weight"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ExactPartitionCounting.boltzmann_weight"),
                H("boltzmann weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rational weight agrees with the actual real exponential at inverse temperature log 2 and energy (n+1) times the violation count."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("penalty-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/ExactPartitionCounting.penalty_sum"),
                H("penalty sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The total diagonal penalty is the sum of the syntactically constructed individual clause penalties."))), DescribeRole.Theorem))));
}
