using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class UnitaryAverageLeakageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the averaging operation and derive quantitative commutator bounds using the C-star norm. A separate Weyl/partial-trace identification is required for the full physical leakage theorem.", H("Operator-Norm Leakage of Finite Unitary Averages"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conjugate-norm"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugate_norm"),
                H("conjugate norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conjugation-defect-norm"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/UnitaryAverageLeakage.conjugation_defect_norm"),
                H("conjugation defect norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("average-norm-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_norm_le"),
                H("average norm le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("average-defect"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect"),
                H("average defect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("average-defect-le-leakage"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/UnitaryAverageLeakage.average_defect_le_leakage"),
                H("average defect le leakage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The average and maximum are explicitly constructed. Triangle inequality and right-unitary invariance prove that the average defect is bounded by the largest measured commutator. No contraction conclusion is assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("leakage-le-twice-norm"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_le_twice_norm"),
                H("leakage le twice norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centered-leakage-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/UnitaryAverageLeakage.centered_leakage_bounds"),
                H("centered leakage bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This specialization has an explicit zero-average hypothesis. It must be discharged by a concrete twirl theorem before being cited for the interaction V of the theory."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("leakage-eq-zero-iff"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/UnitaryAverageLeakage.leakage_eq_zero_iff"),
                H("leakage eq zero iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sum-isometry-defect-sq"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/UnitaryAverageLeakage.sum_isometry_defect_sq"),
                H("sum isometry defect sq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite-sum polarization gives the exact Hilbert-space square identity. Identification of conjugation as a Hilbert-Schmidt isometry and all dimension normalizations remain separate."))), DescribeRole.Theorem))));
}
