using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class PrimePowerGcdHorizonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/PrimePowerGcdHorizon.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nilpotent scalar lift makes the omitted gcd block recoverable and gives the exact higher-prime-power horizon, including bounded natural-source witnesses.",
        H("Sharp Prime-Power Fibonacci Gcd Horizons"),
        Blocks(
            Node("signedObservation", "Signed Fibonacci observations",
                "For arbitrary integers n,z and natural time k, Y(k)=F(k-1)n+F(k)z, "
                + "where the Fibonacci sequence is extended to integer indices. Thus Y(0)=n, "
                + "Y(1)=z and Y(k+2)=Y(k+1)+Y(k). A signed gcd observation is "
                + "gcd(abs(Y(k)),P); the absolute value is retained for negative observations.",
                DescribeRole.Definition),
            Node("sourceObservation", "Actual natural sources",
                "A source is any pair of natural numbers a,b. Its observation at natural "
                + "time k is F(k+3)a+F(k+4)b. The associated initial pair is "
                + "(2a+3b,3a+5b), and the signed recurrence agrees with this natural "
                + "observation at every time. No fixed initial-quantity fiber or primitive "
                + "restriction is imposed.", DescribeRole.Definition),
            Node("horizon", "The local horizon",
                "For prime p and e at least 2, put P=p^e, q=p^(e-1), r=zeroRank(P) "
                + "and R=zeroRank(q), using the least positive Fibonacci zero rank. "
                + "The horizon is T=r when r=R and T=r-R otherwise. The theorem proves "
                + "that the only alternative is r=pR, so the growth horizon is (p-1)R.",
                DescribeRole.Definition),
            Node("sharp_prime_power_gcd_horizon", "The exact unconditional horizon",
                "For every prime p and every natural e at least 2, all ranks zeroRank(p^j), "
                + "for every natural j, exist, are positive, have divisible Fibonacci numbers "
                + "and are minimal among positive divisible indices. Moreover r=R or r=pR. "
                + "The following three clauses hold jointly. First, for every four integers "
                + "n,z,n2,z2, equality of gcd(abs(Y(k)),P) for every positive k at most T "
                + "implies equality at every positive time. Second, for every four natural "
                + "numbers a,b,a2,b2, equality of the actual-source gcd observations at "
                + "every positive k at most T implies equality at every positive time. "
                + "Third, there exist natural a,b,a2,b2, each strictly below P, whose "
                + "observations agree for all 1<=k<T, while their terminal gcds at T "
                + "are respectively P and q. This includes p=2, p=5, stagnant lifts, "
                + "zero states and saturated states. Neither time zero nor a supplied rank "
                + "or orbit-classification hypothesis is used in the conclusion.",
                DescribeRole.Theorem,
                "Finite invertible Fibonacci dynamics modulo every positive modulus gives "
                + "a cyclic action on the finite residue-state set and a positive return, "
                + "hence a positive minimal zero index. Scalar unit multiplication preserves "
                + "gcd observations even when the state itself has a longer return. Strong divisibility "
                + "identifies its zero indices with its multiples. Write a=F(R-1), b=F(R). "
                + "Adjacent Fibonacci coprimality makes a a p-unit. Since q divides b and "
                + "e>=2, both b^2 and pb vanish modulo P. The actual shift is "
                + "Y(s+R)=aY(s)+bY(s+1). Iteration yields "
                + "aY(s+iR)=a^i(aY(s)+ibY(s+1)) modulo P. Therefore the return at pR "
                + "is scalar; the entry-point theorem gives R dividing r and r dividing pR, "
                + "which proves the two rank alternatives.",
                "In a growth step write b=qc; c is a p-unit. If a primitive state has "
                + "Y(s)=qu, its top-precision zero condition in block i is "
                + "au+icY(s+1)=0 modulo p. The companion Y(s+1) is a p-unit, since "
                + "otherwise both adjacent coordinates would be p-divisible. This affine "
                + "line has exactly one root among the p block positions. Consequently "
                + "the last position is a full-P hit exactly when none of the first p-1 "
                + "positions is. The lower-modulus gcd is R-periodic. If there is no q-hit, "
                + "there can be no top hit. Nonprimitive states have R-periodic full gcds, "
                + "because the off-diagonal product vanishes modulo P. The first two paid "
                + "readings recover that flag. Since R>=3, even p=2 supplies them. Thus "
                + "the paid (p-1)R readings determine the final block, and the scalar gcd "
                + "period pR determines all positive times. In a stagnant step b vanishes "
                + "already modulo P, and scalar return at R proves the upper bound directly.",
                "For sharpness use K(t)=(F(t),-F(t-1)); its reading has absolute value "
                + "F(t-k) for k<=t. In growth choose K((p-1)R) and K(pR). Their lower "
                + "gcd words agree by scalar return modulo q, and neither has an earlier "
                + "full-P hit by the exact rank pR. At T the first is zero and the second "
                + "has gcd q, since q divides F(R) but P does not. In stagnation choose "
                + "K(R) and K(R)+(q,0). They agree modulo q and neither has a positive "
                + "q-zero before R. At R their gcds are P and gcd(qF(R-1),P)=q. "
                + "For each signed state pull back by the determinant-one inverse "
                + "C inverse=((5,-3),(-3,2)), then take least nonnegative representatives "
                + "modulo P. Multiplying back by C=((2,3),(3,5)) recovers the signed "
                + "state modulo P, preserving every gcd and giving all four source "
                + "coordinates strictly below P."))));

    private static DocumentBlock Node(string name, string title, string statement,
        DescribeRole role, params string[] proof) => Describe.Lean(
            DescribeId.Create("prime-power-gcd-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(statement)), .. proof.Select(text => Paragraph(Text(text)))]), role);
}
