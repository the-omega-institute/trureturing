using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class EtaOddOccupationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/EtaOddOccupation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The independently counted odd-occupation series has an exact Dedekind eta normalization and an even-rank S transformation.",
        H("Eta and Odd Occupations"),
        Blocks(
            Paragraph(Text("For rank r, let a(r,N) be the cardinality of the finite odd-weight occupation fibre on Fin(r) times N. ColouredOddOccupation identifies this fibre with a finite dependent partition antidiagonal. AnalyticOddOccupation proves absolute convergence and the ordinary complex Euler product for the series H(r,q)=sum over N of a(r,N)*q^N whenever norm(q)<1. The coefficients are independent of the product and of the eta function.")),
            Node("oddCoefficientSeries", "The coefficient series",
                "For every natural rank r and complex q, oddCoefficientSeries(r,q) is the complex infinite sum of a(r,N)*q^N. Its convergence inside the unit disk is supplied by summable_norm_odd_coefficients. Rank zero and q=0 belong to that convergence statement.", DescribeRole.Definition),
            Paragraph(Text("Mathlib's DedekindEta and Discriminant modules supply eta, its upper half-plane nonvanishing, and eta(-1/tau)=sqrt(I) inverse * sqrt(tau) * eta(tau). These results are due to Chris Birkbeck and David Loeffler under Apache 2.0. The product separation uses tprod_even_mul_odd. The normalization below follows by splitting the eta product at tau/2 into its even and odd factors and comparing its exponential prefactors.")),
            Node("normalized_odd_character_eq_eta", "Exact eta normalization",
                "For every natural r, arbitrary complex c and complex tau with positive imaginary part, c*exp(2*pi*I*tau*r/48)*H(r,exp(pi*I*tau)) equals c*(eta(tau)/eta(tau/2))^r. The positive imaginary part ensures norm(exp(pi*I*tau))<1. Nonvanishing is used for eta(tau/2); no nonvanishing assumption is imposed on c. All complex phases and r=0 are included.", DescribeRole.Theorem),
            Node("normalized_odd_character_S", "The even-rank S transformation",
                "For every natural m, arbitrary complex c and tau with positive imaginary part, c*exp(2*pi*I*(-1/tau)*(2*m)/48)*H(2*m,exp(pi*I*(-1/tau))) equals c*((2^m) inverse)*(eta(tau)/eta(2*tau))^(2*m). Apply eta's S formula at tau and 2*tau. Squaring the ratio of square-root factors gives 1/2 by Complex.cpow_nat_inv_pow, and raising this identity to m gives precisely 2^(-m). No multiplicative law for principal square roots is used. Both m=0 and c=0 are included.", DescribeRole.Theorem),
            Paragraph(Text("LatticeHalfFockCharacter consumes both scalar identities for c equal to the trace of an arbitrary ActualGround endomorphism. Its character is defined from the restricted traces on the original tensor L0 kernels. The finite supplier proves all-grade finite-dimensionality, preservation by id tensor A and coefficient identification; the analytic bridge proves absolute summability before applying these eta identities. No Monster vacuum, parity projection, orbifold construction, lift, physical CFT, string theory or spacetime conclusion follows from these scalar formulas alone."))),
        []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("eta-odd-occupation-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
