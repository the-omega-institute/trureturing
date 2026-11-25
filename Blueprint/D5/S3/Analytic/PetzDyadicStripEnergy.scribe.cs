using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PetzDyadicStripEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For faithful bipartite matrices, the partial-trace Umegaki loss splits into dyadic logistic boundary energies and an exact remainder.",
        H("Dyadic decomposition of the strip energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petz-dyadic-strip-remainder"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicStripEnergy.remainder_eq_two_mul_stripGram_half"),
                H("Strip Gram at half frequency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The remainder after subtracting the logistic Gram of the boundary jump equals twice the exact strip Gram entry at half of each frequency. The identity holds for every pair of real frequencies, including coincident and zero frequencies.")),
                    Paragraph(Text("This is identity (2) of the project derivation Exact dyadic deficit decomposition for an actual mixed retained state. For a nonzero frequency difference, the hyperbolic double-angle identities give the relations between the logistic and coth factors at the two scales. At frequency difference zero both factors take the value one. The exponential addition law then matches the jump coefficients at either scale."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-strip-energy"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy"),
                H("Exact strip quadratic energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take the real part of the finite quadratic form with the closed strip Gram as its kernel and complex coefficients paired by conjugation in the first argument."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-logistic-energy"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicStripEnergy.logisticEnergy"),
                H("Logistic boundary energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply each complex coefficient at frequency x by 1 minus exp(x/2). Integrate the squared norm of the resulting Fourier sum against pi/(cosh(2 pi t) + 1) on the real line."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-strip-decomposition"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic"),
                H("Exact finite dyadic decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary finite real frequencies and complex coefficients, and every natural cutoff M, the strip energy equals the sum over scales m from zero up to M of the logistic energies at frequencies divided by 2^m, each weighted by 2^m. The sum excludes scale M. Add 2^M times the strip energy at frequencies divided by 2^M.")),
                    Paragraph(Text("The logistic Fourier transform identifies each integral with the quadratic form of the boundary jump. Applying the half-frequency identity inside the quadratic form gives the induction step while keeping the coefficient family fixed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-strip-lower-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicStripEnergy.stripEnergy_dyadic_lower_bound"),
                H("Finite dyadic lower bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At every natural cutoff the sum of the weighted logistic energies is nonnegative and lies below the original strip energy, for the same arbitrary finite families.")),
                    Paragraph(Text("The logistic integrals have nonnegative integrands. Apply positivity of the closed remainder to the doubled frequency family to obtain positivity of the strip energy at any scale."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-physical-frequency"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicStripEnergy.physicalFrequency"),
                H("Joint and retained log frequency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a joint eigenvector pair of the source and reference and a retained eigenvector pair of their marginals, the frequency is the reference joint log eigenvalue minus the source joint log eigenvalue plus the source marginal log eigenvalue minus the reference marginal log eigenvalue. Faithfulness gives positive eigenvalues for both actual partial traces."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-physical-coefficient"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicStripEnergy.physicalCoefficient"),
                H("Physical spectral coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take the joint source and reference eigenbasis entry of the source square root times the lifted source and reference marginal rank-one projections in that order. The environmental factor of each lift is the identity. The indexing keeps every eigenvector, including repeated eigenvalues."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-umegaki-identity"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicStripEnergy.umegakiLoss_eq_stripEnergy"),
                H("Partial-trace entropy loss as a spectral quadratic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any pair of faithful joint matrices on a finite retained space times a finite nonempty environment, subtract the Umegaki trace-log expression of their actual marginals from that of their joint matrices. This equals the sum over all joint eigenvector pairs of the strip quadratic on their physical frequencies and coefficients.")),
                    Paragraph(Text("The source edge is the source square root times the two lifted projections. The reference edge is the product of the two lifted projections times the reference square root and the square root of the marginal eigenvalue ratio. Partial-trace adjunction reduces both Hilbert–Schmidt Gram matrices to the same diagonal. The joint frequency shift cancels from the kernel differences, so the logistic and hyperbolic cotangent terms cancel after the joint summation. The remaining linear frequency is the trace pairing with the joint and marginal logarithms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-umegaki-finite"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicStripEnergy.umegakiLoss_dyadic"),
                H("Exact finite decomposition and lower estimate for Umegaki loss"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any natural cutoff M and faithful joint pair as above, sum the logistic boundary energy over joint eigenvector pairs and over levels m less than M. Each level uses the physical frequencies divided by 2^m and the original coefficients, with weight 2^m. The sum is nonnegative and bounded above by the Umegaki loss. The difference is the sum of the physical strip quadratics at frequencies divided by 2^M, with weight 2^M."))),
                DescribeRole.Theorem))));
}
