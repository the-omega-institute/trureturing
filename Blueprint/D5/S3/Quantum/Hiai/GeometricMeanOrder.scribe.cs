using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class GeometricMeanOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GeometricMeanOrder", H("GeometricMeanOrder"), Blocks(
            Describe.Lean(DescribeId.Create("mean-eq-operatorPowerMean"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_eq_operatorPowerMean"),
                H("Base convention"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every complete nontrivial complex Hilbert space, nonnegative A and strictly positive B, the base-first genuine mean equals operatorPowerMean(theta,1,A,B). No order of multiplication is reversed. The inner congruence is nonnegative and all inverse powers apply to the strictly positive base."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-pd"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_pd"),
                H("Strict positivity"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every real theta the mean of two strictly positive operators is strictly positive. Both invertible square-root congruences and the inner spectral power preserve strict positivity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-jointlyConcave"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_jointlyConcave"),
                H("Joint mean concavity"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every theta in [0,1] the genuine mean is jointly operator concave on the strictly positive cone. The existing all-Hilbert perspective theorem supplies this inequality with the local base in its second argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-mono-left"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono_left"),
                H("Monotonicity of the base"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("If B <= Bprime are strictly positive and A is nonnegative, increasing B increases its genuine mean with A for every theta in [0,1]. Set C=sqrt(B) sqrt(Bprime inverse); C adjoint C <= I. Contraction Jensen for the negative power function gives the required middle inequality. Congruence by sqrt(Bprime) cancels the invertible factors. No B/A commutation is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-mono-right"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono_right"),
                H("Monotonicity of the other input"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("Increasing A increases the genuine mean with fixed B, for theta in [0,1]. Loewner-Heinz monotonicity is applied between the two square-root congruences. The both-input theorem uses this inequality after increasing the base."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-mono"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono"),
                H("Both-input order"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("Increasing both strictly positive bases and the nonnegative second inputs increases the mean for theta in [0,1]. The comparison composes base monotonicity and Loewner-Heinz monotonicity."))), DescribeRole.Theorem),
            Paragraph(Text("These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration is claimed.")))));
}
