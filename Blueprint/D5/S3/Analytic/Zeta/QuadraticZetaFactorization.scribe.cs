using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class QuadraticZetaFactorizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero prime ideals are partitioned by their actual contraction to the rational integers. The convergent HasProd supplier justifies regrouping by rational primes. The actual local factors, including two and the ramified prime, then prove zeta_K=zeta_Q*L for real part greater than one.", H("QuadraticZetaFactorization"), Blocks(
            Paragraph(Text("Nonzero prime ideals are partitioned by their actual contraction to the rational integers. The convergent HasProd supplier justifies regrouping by rational primes. The actual local factors, including two and the ramified prime, then prove zeta_K=zeta_Q*L for real part greater than one.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("quadraticzetafactorization-primeidealsoverequiv"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticZetaFactorization.primeIdealsOverEquiv"), H("primeIdealsOverEquiv"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Nonzero maximal-order prime ideals, partitioned by their actual contraction to Z. This equivalence includes ramified primes."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quadraticzetafactorization-hasprod-rationalprime-factors"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticZetaFactorization.hasProd_rationalPrime_factors"), H("hasProd_rationalPrime_factors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Genuine convergent regrouping of the Dedekind Euler product by rational primes. `HasProd` is required here: a bare equality of `tprod` expressions does not justify it."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticzetafactorization-primeideal-euler-factor"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticZetaFactorization.primeIdeal_euler_factor"), H("primeIdeal_euler_factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The actual maximal-order Euler factor, including the factors at two and p."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticzetafactorization-dedekindzeta-eq-riemannzeta-mul-lfunction"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticZetaFactorization.dedekindZeta_eq_riemannZeta_mul_LFunction"), H("dedekindZeta_eq_riemannZeta_mul_LFunction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Quadratic Dedekind-zeta factorization for the actual number field and actual Legendre Dirichlet character, proved by convergent local-to-global products."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Zeta/PrimeQuadraticLValues")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization"))]));
}
