using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class QubitPhysicalRepairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalize retained isometry columns to compare the actual physical output with pointer outputs. Conditional density blocks and orthogonal pointer entropies give a classical Markov repair even at zero weights. A common normalized environment vector instead gives an AB-C product repair.",
        H("Normalized physical repairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qcmi-product-right"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.qcmi_product_right"),
                H("A product across AB and C"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every density state P on A times B and every density state gamma on C, relabeling P tensor gamma onto A times (B times C) gives ordinary conditional mutual information zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("classicalmarkovstate"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.classicalMarkovState"),
                H("An orthogonal pointer state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A probability vector on B and normalized conditional states alpha(j) on A and gamma(j) on C define the mixture of alpha(j) tensor the computational pointer j tensor gamma(j). Zero weights do not require division."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qcmi-classicalmarkovstate"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.qcmi_classicalMarkovState"),
                H("Conditional independence in every pointer block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The orthogonal pointer mixture has ordinary conditional mutual information zero. Each of its four actual marginal entropies is evaluated using product additivity and the orthogonal record entropy formula; the classical entropy and both conditional entropy sums cancel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("isometry-operatornorm-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.isometry_operatorNorm_le"),
                H("Operator norm of an isometry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite matrix with orthonormal columns has operator norm at most one, including empty coordinate types."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pointerisometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.pointerIsometry"),
                H("A normalized retained-column pointer map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two environment vectors define a qubit map whose j-th column has support only on output pointer j. Unit norms make this map an isometry."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-pointer-isometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.normalized_pointer_isometry"),
                H("Normalize retained columns below unit flip probability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the sum s squared of the two flip probabilities is below one, both retained columns of the actual isometry have positive norm. Normalize them and delete the flips to obtain a pointer isometry within operator norm 2s. No input block weight is inverted."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physicaloutput-distance"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.physicalOutput_distance"),
                H("A common environment comparison"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two physical isometries applied to the same AB density state, followed by discarding their common environment, differ in half trace distance by at most the operator norm of the difference of the isometries. This comparison has no reference-dimension factor."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pointerinput-distance"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.pointerInput_distance"),
                H("The cost of deleting qubit coherence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pinching an actual AB density state in the two-dimensional B basis changes it in half trace distance by at most the trace norm of its complex off-diagonal A block. The two conjugate off-diagonal terms and the half-distance convention account for the factor."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("classical-pointer-repair"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.classical_pointer_repair"),
                H("A classical repair on the same physical system"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let W be an actual dilation of T, and let s squared be its total flip probability in the chosen qubit basis. If s squared is below one, normalizing its two retained vectors and pinching the actual AB input produces a classical Markov state on the same ABC carrier. Its half trace distance from rho is at most r plus the trace norm z of the actual off-diagonal AB block plus 2s. A positive block weight normalizes its conditional A state; a zero block has zero positive matrix and needs no division."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-environment-product-repair"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitPhysicalRepair.common_environment_product_repair"),
                H("A common environment gives an AB-C product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let g be the modulus of one minus the inner product of the two retained Stinespring vectors. If the total flip probability s squared is below one, normalize the first retained vector and use it for both pointer columns. This is a physical product across AB and C, with ordinary qcmi zero and half trace distance from rho at most r plus 2s plus the square root of 2g. The comparison retains every rank and the same ABC system."))), DescribeRole.Theorem))));
}
