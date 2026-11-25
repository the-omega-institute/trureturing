using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio.Weighted;

internal sealed class CompositionGcdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous floor minima, universal weighted factorial certificates, and actual ideal norms.",
        H("Weighted factorial gcds and residue-degree norm complements"),
        Blocks(
            Paragraph(Text(
                "Nonnegative weights preserve the prime-power minima of a composition. "
                + "The key is simultaneous attainment for every power of one rational prime. "
                + "For number fields the relevant weights come from the residue degrees of actual "
                + "prime ideals, and the complementary weights are nonnegative by the degree formula. "
                + "The full-ring factorial terminology refers to the prime-ideal Euler formula of "
                + "Bhargava and Chabert-Cahen; a p-ordering construction is not an additional object here.")),
            Describe.Lean(
                DescribeId.Create("floor-profile"),
                DeclarationHandle.Create(Prefix + "floorProfile"),
                H("Floor profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite tuple a and a positive modulus q, sum floor(a(i)/q) over all parts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("floor-minimum"),
                DeclarationHandle.Create(Prefix + "floorMinimum"),
                H("Composition floor minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For M<=H, write Q(q)=max(0,floor(H/q)-M). Natural subtraction implements this truncation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-exponent"),
                DeclarationHandle.Create(Prefix + "weightedExponent"),
                H("Weighted prime exponent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The index j starts at zero and represents the modulus p^(j+1). Sum c(p,j)*floor(n/p^(j+1)) for 0<=j<=H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-value"),
                DeclarationHandle.Create(Prefix + "weightedValue"),
                H("Weighted factorial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For inputs n<=H, take the product over rational primes p<=H of p raised to the weighted exponent. Every omitted prime or power has zero floor contribution, so a finite cutoff represents arbitrary natural coefficient arrays."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-product"),
                DeclarationHandle.Create(Prefix + "weightedProduct"),
                H("Weighted composition product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply the weighted factorials of the entries of a finite tuple, using the same cutoff and coefficients for every entry."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-tail"),
                DeclarationHandle.Create(Prefix + "weightedTail"),
                H("Weighted tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take the product over primes p<=H of p raised to sum c(p,j)*Q(p^(j+1)) for 0<=j<=H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-prime-ideal"),
                DeclarationHandle.Create(Prefix + "NumberFieldNorm.rationalPrimeIdeal"),
                H("Rational prime ideal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ideal (p) of the integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("primes-above"),
                DeclarationHandle.Create(Prefix + "NumberFieldNorm.primesAbove"),
                H("Primes over a rational prime"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a number field K, use the actual finite set of prime ideals of its ring of integers above (p)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("norm-weight"),
                DeclarationHandle.Create(Prefix + "NumberFieldNorm.normWeight"),
                H("Residue-degree norm weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the exponent j+1, sum the residue degree f(P) over primes P above p for which f(P) divides j+1. These are the coefficients obtained from NP=p^f(P)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("residue-factorial-ideal"),
                DeclarationHandle.Create(Prefix + "NumberFieldNorm.residueFactorialIdeal"),
                H("Euler ideal in rational coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply P raised to sum of floor(n/p^(j+1)) over indices for which f(P) divides j+1. The outer rational primes satisfy p<=H and the indices satisfy j<=H. This is an ideal of the actual ring of integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("full-ring-factorial-ideal"),
                DeclarationHandle.Create(Prefix + "NumberFieldNorm.fullRingFactorialIdeal"),
                H("Full-ring Euler factorial ideal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each rational prime p<=n and each prime ideal P above p, use the exponent sum floor(n/(NP)^(j+1)) for 0<=j<=n. This finite prime-ideal Euler product is the full-ring factorial presentation. The comparison with rational coordinates reindexes j+1 by multiples of the actual residue degree, and increasing the cutoff above n leaves the ideal unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("norm-complement"),
                DeclarationHandle.Create(Prefix + "NumberFieldNorm.normComplement"),
                H("Integral norm complement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divide (n!)^d by the absolute norm of the Euler factorial ideal, where d=[K:Q]. The norm and complement theorem proves exact divisibility and identifies this quotient with the complementary weights d-c(p,j)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("simultaneous-floor-minimum"),
                DeclarationHandle.Create(Prefix + "simultaneous_floor_minimum"),
                H("One composition for every power of a fixed prime"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let S consist of the (M+1)-tuples of natural numbers summing to H-M, with M<=H. For every fixed rational prime p, one a in S satisfies sum floor(a(i)/p^j)=Q(p^j) for every j>=1. The quotient-remainder identity bounds each sum below by Q. The existing factorial gcd theorem supplies a composition attaining the sum of these lower bounds. Equality of finite sums of ordered natural coordinates forces equality in every coordinate. Powers beyond the finite cutoff contribute zero. A different rational prime may require a different composition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-composition-gcd"),
                DeclarationHandle.Create(Prefix + "weighted_composition_gcd"),
                H("Exact weighted composition gcd"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every array of natural coefficients c, the gcd over S of the weighted composition products equals the weighted tail. Every composition gives the coordinatewise lower bounds. For each prime p the simultaneous composition attains all of its weighted bounds, including when some or all coefficients vanish. Primewise divisibility in both directions proves the exact natural-number equality. No single composition is asserted to minimize all rational primes simultaneously."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-certificate-is-universal"),
                DeclarationHandle.Create(Prefix + "exact_certificate_is_universal"),
                H("Ordinary factorial certificates are universal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let C be a finite subfamily of S whose ordinary factorial products have gcd tailLCM(H,M). Then the same C has the exact weighted gcd for every natural coefficient array. For each p, if all members had strictly larger p-valuation than the tail, the next power of p would divide their gcd, a contradiction. A member attaining the ordinary valuation saturates every p-power floor bound, so it also attains every nonnegative weighted bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("small-universal-certificate"),
                DeclarationHandle.Create(Prefix + "exists_small_universal_certificate"),
                H("A prime-counting bound for a universal family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Set t=floor(H/(M+1)). There is a family C of size at most pi(t)+1 that is exact for ordinary factorials and for every natural weighting. One composition has every entry at most t; the residue bound H mod (M+1)<=M proves its feasibility. Add one p-specific composition for each prime p<=t. These members attain the small-prime valuations. For p>t the bounded composition has valuation zero. Duplicate compositions can only reduce the cardinality. The argument includes t=0, M=H, and H=M=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("number-field-norm-and-complement"),
                DeclarationHandle.Create(Prefix + "NumberFieldNorm.number_field_norm_and_complement"),
                H("Actual ideal norms and complementary composition gcds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual number field K, the residue-degree weights satisfy c(p,j)<=d. Indeed c(p,j)<=sum f(P)<=sum e(P)f(P)=d. The Euler ideal has absolute norm equal to the weighted factorial: multiplicativity of the ideal norm gives NP=p^f(P), and exchanging the finite sums gives precisely the divisibility-indexed weights. The local reindexing and cutoff comparison identify this with the Euler product using floor(n/(NP)^j). The quotient (n!)^d/NF(n) is the weighted factorial with coefficients d-c(p,j), so it is an integer. The two composition gcds are their respective weighted tails, and their product is tailLCM(H,M)^d. The proof uses common rational-prime compositions; it never moves the ideal norm through a gcd. This statement uses the Euler-product presentation of the full-ring factorial. It does not identify the weighted tail with the norm of a product of intersections of all integral ideals of bounded norm."))),
                DescribeRole.Theorem))));
}
