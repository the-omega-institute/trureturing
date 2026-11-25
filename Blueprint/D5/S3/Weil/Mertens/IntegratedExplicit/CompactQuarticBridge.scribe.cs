using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CompactQuarticBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quartic Riemann hypothesis criteria for tail LCMs and compact factorial gcds",
        H("An exact finite arithmetic test"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tail-lcm-mangoldt-sum"),
                DeclarationHandle.Create(Prefix + "log_tailLCM_eq_sum_vonMangoldt"),
                H("Exact logarithm of the tail LCM product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive M and natural N, put H=MN. Expand the logarithm of each "
                    + "prefix LCM as the Chebyshev psi sum. The incidence a*k<=H with "
                    + "M<k<=H and 1<=a<=N is equivalent to k<=floor(H/a), so exchanging "
                    + "the two finite sums gives the Mangoldt weight floor(H/a)-M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centered-tail-log"),
                DeclarationHandle.Create(Prefix + "D"),
                H("Centered normalized tail logarithm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divide the log tail product at H=MN by M and subtract "
                    + "N log N minus (1+EulerMascheroniConstant)N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tail-rounding-bounds"),
                DeclarationHandle.Create(Prefix + "U_sub_D_bounds"),
                H("Explicit one-sided floor error"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtract the centered tail logarithm from CompleteMertensPeak.U(N). "
                    + "The exact difference is the sum of the Mangoldt weights times "
                    + "MN/a-floor(MN/a), divided by M. Each floor error is in [0,1), "
                    + "yielding the nonnegative upper bound psi(N)/M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tail-quartic-blocks"),
                DeclarationHandle.Create(Prefix + "rh_iff_tailLCM_quartic_integer_blocks"),
                H("Cofinal quartic blocks for the tail LCM"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At N=n^4 and M=n^2 the floor error is at most (log 4+4)n^2. "
                    + "For each positive exponent loss and natural threshold, choose a smaller "
                    + "positive loss and a block sufficiently far out to absorb the error. "
                    + "The original quartic integer-block criterion then transfers in both directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tail-quartic-constant"),
                DeclarationHandle.Create(Prefix + "rh_iff_eventually_tailLCM_quartic_constant"),
                H("Eventual fixed-constant criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "RH supplies the eventual quadratic bound with constant one. Conversely "
                    + "any eventual fixed real multiple of n^2 is absorbed into each positive "
                    + "quartic power loss on all sufficiently large blocks."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tail-quartic-mass-threshold"),
                DeclarationHandle.Create(Prefix + "rh_iff_eventually_tailLCM_quartic_of_mass_lt"),
                H("A sufficient fixed constant above the first Li mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every constant C strictly above firstLiMass, the sharp actual envelope "
                    + "under RH bounds U(n^4)/n^2 eventually by C via y=4 log n. "
                    + "The nonnegative rounding error transfers this bound to the tail. "
                    + "The fixed-constant criterion gives the converse."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quartic-factorial-gcd"),
                DeclarationHandle.Create(Prefix + "quarticFactorialGcd"),
                H("The compact gcd at the fourth-power scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Set M=n^2, N=n^4, r=M+1 and s=M(M-1). The gcd is the "
                    + "gcd of selbergFactorial(r,s,b) for 0<=b<=floor(s/r), where "
                    + "each term is the product over j=1,...,r of (jb)!/b! times "
                    + "(s-(r-j)b)!."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quartic-family-size"),
                DeclarationHandle.Create(Prefix + "quarticFactorialGcd_family_size"),
                H("Quadratic family size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive n, the number of admissible integer parameters "
                    + "is at most n^2 because M(M-1)<M(M+1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-centered-log"),
                DeclarationHandle.Create(Prefix + "compactD"),
                H("Centered normalized compact gcd logarithm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Apply the same real normalization and centering at N=n^4 and M=n^2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compact-quartic-error"),
                DeclarationHandle.Create(Prefix + "compactD_U_bounds"),
                H("Two-sided quantitative comparison with the integrated remainder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact degree identity rs+r-1=M^3 gives the tail product at "
                    + "H=MN with no padding. The compact factorial theorem bounds the gcd "
                    + "between the tail and the tail times B!, where B=2(M+1)^2. "
                    + "The logarithmic gap after division by M is between zero and B log B/M. "
                    + "For n>=2, B<=8n^4 and log B<=7 log n. Combining with the floor bound "
                    + "places the compact centered remainder minus U(n^4) between "
                    + "-(log 4+4)n^2 and 56n^2 log n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-quartic-rh"),
                DeclarationHandle.Create(Prefix + "rh_iff_compact_factorial_gcd_quartic_integer_blocks"),
                H("RH equivalence for the explicit compact factorial family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive real kappa and natural A there must exist k>=max(A,2) "
                    + "such that every integer n in [k^3,k^4] satisfies the centered log gcd "
                    + "bound (n^4)^(1/2+kappa). The gcd ranges over the explicit factorial family "
                    + "with r=n^2+1 and s=n^2(n^2-1). The quantitative error in either direction "
                    + "is eventually absorbed by any positive quartic power loss. Choose the "
                    + "threshold for this absorption before selecting the block at half the "
                    + "requested loss. The canonical quartic criterion gives the equivalence."))),
                DescribeRole.Theorem))));
}
