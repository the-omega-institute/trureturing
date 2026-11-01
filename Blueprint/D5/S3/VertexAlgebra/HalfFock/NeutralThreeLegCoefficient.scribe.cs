using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;

internal sealed class NeutralThreeLegCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual full neutral corrected-field coefficients equal the finite raw three-leg coherent Gaussian coefficients on arbitrary ground tensors.",
        H("Actual neutral three-leg Gaussian coefficient identity"),
        Blocks(
            Paragraph(Text("This unit identifies the finite raw coherent exponential coefficient with the actual neutral correctedField coefficient on the original tensor carrier, using output-projected mode restriction and finite scalar Laurent realization. Source, input and output occupations may have arbitrary repetitions. The Gram matrix is the original raw matrix, the only invertibility assumption is the native hu, and rank zero is included.")),
            Paragraph(Text("Write F(d,h,l) for the actual finite Laurent entry. Source insertion gives the sum of SO(a,j) F(d,h,l-single(j)) over occupied output labels, h(j) SI(a,j) F(d,h-single(j),l) over occupied input labels, and d(b) SS(a,b) F(d-single(b),h,l) over occupied source labels. Creation has no output multiplicity; annihilation has the input multiplicity. The native zero-source entry is the Kronecker delta h=l. The SS diagonal is p rather than 2p. A source label s>=1 uses native index s-1, so sourceWeight is s; a twisted label k>=0 has frequency k+1/2. These conventions fix the exponents and the raw Gram factors.")),
            Paragraph(Text("The combinatorics is classical labelled-position Wick/Isserlis and the exponential formula: equal labels are distinct positions, so diagonal pairing counts have factors 2^m m! and off-diagonal counts m!. Wick (1950, Physical Review 80, 268) and Isserlis (1918, Biometrika 12, 134-139) supply the classical provenance. OriginalCorrectionGaussian supplies the existing factorial Gaussian moment recurrence and the actual Corr insertion calculus. The source-specific bridge proves that the three-leg moment is l! times F(d,h,l), by source-degree induction and the native IO base; the full Gaussian moment is d! h! l! times the ordinary exponential coefficient. Cancelling l! therefore divides the actual field entry by d! h!, with ordinary output coefficient and no output factorial denominator. No new global novelty, positivity, unitarity, analytic completion, sewing, string-theory completion or AdS/CFT result is asserted.")),
            Describe.Lean(
                DescribeId.Create("native-normal-readout"),
                DeclarationHandle.Create(Prefix + "nativeNormalReadout"),
                H("Linear readout of the actual finite normal action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The monomial basis extends the finite raw normal-mode coefficient action linearly to source polynomials, using the proved input/output frequency box."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-source-insertion"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_source_insertion"),
                H("Actual corrected coefficient source insertion with SS contractions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary repeated occupations and any ground vector, T to the forced exponent times the actual corrected-field coefficient after inserting source a equals the unpaired normal readout times that vector plus the sum over b of d(b) SS(a,b) times the native entry with one b removed, acting by ground identity. The proof evaluates the actual correction lift at T to minus two and reuses its source-partial formula. No Gaussian coefficient equality is assumed. The actual SO/SI lowering theorem computes the unpaired readout and supplies the remaining terms of the full recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-io-base"),
                DeclarationHandle.Create(Prefix + "nativeNeutralLaurentEntry_zero"),
                H("Native identity propagation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With zero source occupation, the actual neutral corrected field has entry one exactly when input and output occupations agree, and zero otherwise. This includes every repeated label and rank zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-unpaired-lowering"),
                DeclarationHandle.Create(Prefix + "nativeNeutralLaurentEntry_unpaired"),
                H("Actual source-output and source-input lowering"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite normal ordering is invariant under permutation of source positions. Its projected coefficient is independent of enlarging the finite mode box. Multiplication by a source variable consequently lowers the output coefficient through SO without multiplicity, or differentiates the input monomial through SI with multiplicity h(j)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-full-recurrence"),
                DeclarationHandle.Create(Prefix + "nativeNeutralLaurentEntry_recurrence"),
                H("Full actual SS/SI/SO insertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combining actual Corr insertion with the unpaired normal readout gives the full coefficient recurrence. Together with native identity propagation it determines all source occupations by induction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-three-leg-matrix"),
                DeclarationHandle.Create(Prefix + "nativeThreeLegMatrix"),
                H("Raw symmetric three-leg matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite labels are tagged source, input and output. The only nonzero blocks are SS, SI, SO and the input-output identity, together with their transposes. Source-source symmetry follows from the actual pair covariance."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-three-leg-occupation"),
                DeclarationHandle.Create(Prefix + "nativeThreeLegOccupation"),
                H("Three tagged occupations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The disjoint sum of source, input and output occupations retains all multiplicities. Its factorial weight is the product of their three factorial weights."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-three-leg-raw-polynomial"),
                DeclarationHandle.Create(Prefix + "nativeThreeLegRawPolynomial"),
                H("Literal SS/2 + SO + SI + IO polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This polynomial is written directly in the source, input and output variables with the raw kernel coefficients. It is proved equal to one half of the symmetric block quadratic, including the repeated-label diagonal convention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-three-leg-exponential-coefficient"),
                DeclarationHandle.Create(Prefix + "nativeThreeLegExponentialCoefficient"),
                H("Finite ordinary exponential coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For total occupation degree N, the ordinary coefficient of the homogeneous quadratic exponential is the coefficient of Q to floor(N/2) divided by floor(N/2) factorial. Odd N gives zero by homogeneity. No infinite analytic series is evaluated."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-restricted-occupation"),
                DeclarationHandle.Create(Prefix + "nativeRestrictedOccupation"),
                H("Restriction to finite occupied labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An occupation is restricted along the inclusion of a finite label set. Whenever that set contains the occupation support, embedding it back reconstructs the original occupation and preserves factorial weight."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-finite-raw-gaussian-coefficient"),
                DeclarationHandle.Create(Prefix + "nativeFiniteRawGaussianCoefficient"),
                H("Raw coherent coefficient on any finite containing set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite coefficient uses the literal raw coherent polynomial and all three restricted occupations. Every finite set containing their supports gives the same actual field entry, so extra unoccupied labels do not change it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-full-raw-gaussian"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_full_raw_gaussian"),
                H("Actual full neutral field equals the raw coherent coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary finite repeated source, input and output occupations, any finite label set containing their supports, the original raw Gram matrix with native IsUnit(det G), every ground vector and every complex unit T, the actual coefficient at its forced exponent, multiplied by T to that exponent and divided by source d! and input h!, equals the ordinary raw coherent exponential coefficient times that same ground vector. The proof establishes the SI/SO lowering and IO base from native operators, then compares factorial moments by induction. It assumes neither a matching formula nor an alternative Gaussian field."))),
                DescribeRole.Theorem))));
}
