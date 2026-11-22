using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class FourPointChannelCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Laurent principal parts of the original four-point channels",
        H("Laurent principal parts of the original four-point channels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-point-laurent-binomial-principal-part"),
                DeclarationHandle.Create(Prefix + "hasPrincipalPart_binomial"),
                H("Finite Laurent extraction with either binomial sign"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let U be analytic at zero and set F(t) = t^(−M) U(t). "
                        + "For a signed mode k, write dₖ for the Taylor coefficient of U of degree M − k − 1 "
                        + "when k < M, and set dₖ = 0 otherwise. For integers M, q, r and ε ∈ {1, −1}, "
                        + "the function t^q (1 + εt)^r F(t) equals a principal part of length max(M − q, 0) "
                        + "plus a remainder analytic at zero, on a punctured neighborhood of zero. Its simple-pole "
                        + "coefficient is the sum of choose(r,j) ε^j d_(q+j) for 0 ≤ j < max(M − q, 0). "
                        + "An empty principal part has simple-pole coefficient zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-point-laurent-lowered-principal-part"),
                DeclarationHandle.Create(Prefix + "hasPrincipalPart_lowered"),
                H("Finite lowering in the reflected channels"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each ℓ < N let Fℓ(t) = t^(−M) Uℓ(t) with Uℓ analytic at zero. "
                        + "The lowering sum uses Fℓ(−t) with weight (−1)^(d+ℓ+2)/ℓ!. "
                        + "Multiply the sum by t^q (1 − t)^r in the first orientation "
                        + "or by t^q (t − 1)^r in the reverse orientation.")),
                    Paragraph(Text("The principal part has length max(M − q, 0). Its simple-pole "
                        + "coefficient sums choose(r,j) (−1)^(d−q+e+ℓ+1) d_(q+j)(Uℓ)/ℓ! "
                        + "over 0 ≤ j < max(M − q, 0) and 0 ≤ ℓ < N, with e = 0 in the first "
                        + "orientation and e = r in the reverse orientation. Reflection contributes "
                        + "(−1)^(−k−1) to the diagonal at mode k, so the j-dependent sign cancels "
                        + "the binomial sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-point-actual-diagonal-numerator"),
                DeclarationHandle.Create(Prefix + "actualDiagonalNumerator_spec"),
                H("The analytic numerator on the signed mode diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let the lattice Gram matrix be positive definite over ℝ and its "
                        + "determinant a unit. For a mod-two charge class a and diagonal sum s, "
                        + "take the Taylor sum of the original coset series rescaled by −1, using right "
                        + "mode E + s − H − K + 1 in degree E. This numerator U is analytic at zero. "
                        + "Its coefficient of degree E is the original coset kernel at modes "
                        + "H + K − E − 1 and E + s − H − K + 1, with the same ordered inputs P, Q, R, S.")),
                    Paragraph(Text("Near zero, U(−z²) = (f(z) + f(−z))/2, where f is the original "
                        + "sewn diagonal for the same charge class and offset s − H − K + 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-point-diagonal-equals-coset-kernel"),
                DeclarationHandle.Create(Prefix + "diagonal_eq_cosetKernel"),
                H("Laurent diagonal equals the original coset kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any numerator satisfying the signed diagonal Taylor identities "
                        + "at s, the coefficient at Laurent exponent −k−1 equals the original "
                        + "coset kernel at modes k and s − k. When k < H + K the corresponding "
                        + "Taylor degree is H + K − k − 1. When k ≥ H + K the degree is negative "
                        + "and the positive definite lattice has an empty energy fiber there."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-point-channel-a-principal-part"),
                DeclarationHandle.Create(Prefix + "hasPrincipalPart_channelA"),
                H("Principal part in channel A"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take the diagonal numerator U at s = m + n + r for the weights "
                        + "H, K and inputs P, Q, R, S. The local channel t^r (1 + t)^m t^(−H−K) U(t) "
                        + "has principal-part length max(H + K − r, 0). The simple-pole coefficient is "
                        + "channelA, the finite sum of choose(m,j) times the coset kernel at "
                        + "modes r + j and m + n − j over that range of j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-point-channel-b-principal-part"),
                DeclarationHandle.Create(Prefix + "hasPrincipalPart_channelB"),
                H("Principal part in channel B"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use weights K, L and ordered inputs Q, R, P, lower^ℓ S "
                        + "with signed diagonal sum m + n + r + ℓ. Sum the resulting Laurent germs "
                        + "at −t with weight (−1)^(m+n+r+ℓ+2)/ℓ! for "
                        + "0 ≤ ℓ < max(H + K + L − m − n − r − 3, 0).")),
                    Paragraph(Text("After multiplication by t^n (1 − t)^r, the principal part has "
                        + "length max(K + L − n, 0), which is also the cutoff for j. The residue channelB uses weight "
                        + "choose(r,j) (−1)^(m+r+ℓ+1)/ℓ! and kernel modes n + j "
                        + "and m + r − j + ℓ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-point-channel-d-principal-part"),
                DeclarationHandle.Create(Prefix + "hasPrincipalPart_channelD"),
                H("Principal part in channel D"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use weights H, L and ordered inputs P, R, Q, lower^ℓ S "
                        + "on the signed diagonal m + n + r + ℓ. The reflected Laurent sum has "
                        + "the same lowering weight (−1)^(m+n+r+ℓ+2)/ℓ! and cutoff "
                        + "max(H + K + L − m − n − r − 3, 0).")),
                    Paragraph(Text("The multiplier t^m (t − 1)^r gives a principal part of length "
                        + "max(H + L − m, 0), which is also the cutoff for j. Reversing the binomial contributes (−1)^r, giving "
                        + "the residue channelD with weight choose(r,j) (−1)^(n+ℓ+1)/ℓ! "
                        + "and kernel modes m + j and n + r − j + ℓ."))),
                DescribeRole.Theorem))));
}
