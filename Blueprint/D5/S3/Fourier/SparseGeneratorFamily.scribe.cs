using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class SparseGeneratorFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform cyclic samples produce symmetric sparse generating sets with a positive ordinary spectral gap.",
        H("Sparse Generator Family"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("char-sum"),
                DeclarationHandle.Create("D5/S3/Fourier/SparseGeneratorFamily.char_sum"),
                H("Character orthogonality at every cyclic frequency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of the standard cyclic character at frequency a is N when a=0 and zero otherwise. Nonunit frequencies and composite cyclic orders remain in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("large-log"),
                DeclarationHandle.Create("D5/S3/Fourier/SparseGeneratorFamily.large_log"),
                H("A lower logarithmic scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The domain N>=ceil(exp(128)) implies log(N)>=128. This controls the sampling and graph-radius estimates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("large-order-pos"),
                DeclarationHandle.Create("D5/S3/Fourier/SparseGeneratorFamily.large_order_pos"),
                H("Positive cyclic order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same domain implies N>0, supplying the nonzero-order instance in the obstruction and its translation-dependent realization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parameters-bounds"),
                DeclarationHandle.Create("D5/S3/Fourier/SparseGeneratorFamily.parameters_bounds"),
                H("Sampling and radius bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For L=log(N), q=ceil(16L) and r=floor(L/16), one has 16L<=q, q+1<=17L, r>=8 and L/32<=r<=L/16."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tolerance-bounds"),
                DeclarationHandle.Create("D5/S3/Fourier/SparseGeneratorFamily.tolerance_bounds"),
                H("Calibration tolerance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The observation tolerance pi/(2r) is positive and at most pi/16, which is strictly below 1/4. These bounds apply to the complete generator rows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("volume-numeric-bound"),
                DeclarationHandle.Create("D5/S3/Fourier/SparseGeneratorFamily.volume_numeric_bound"),
                H("Commutative walk volume"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural p<=34log(N), choose(p+r,r)<=sqrt(N). A weighted binomial term bounds this volume; it controls the support of the graph-distance phase."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("family-set-good"),
                DeclarationHandle.Create("D5/S3/Fourier/SparseGeneratorFamily.familySet_good"),
                H("Symmetric sparse families at every large order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed choice familySet(N) excludes zero, is symmetric under negation, has cardinality 2ceil(16log(N)), and has ordinary squared-character-chord gap at least one. Uniform independent samples exclude signed collisions and two-torsion while controlling every nonzero frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gap-generating"),
                DeclarationHandle.Create("D5/S3/Fourier/SparseGeneratorFamily.gap_generating"),
                H("Positive gap forces generation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any cyclic Finset S, a positive ordinary gap forces its additive subgroup closure to be the full cyclic group. An annihilating frequency would have zero chord average; the finite annihilator cardinality identity then forces generation."))),
                DescribeRole.Theorem))));
}
