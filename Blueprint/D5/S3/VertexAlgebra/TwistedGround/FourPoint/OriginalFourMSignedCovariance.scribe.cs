using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSignedCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native signed Gaussian covariance and source",
        H("Mode sums and the elliptic half-coordinate"),
        Blocks(
            Describe.Lean(DescribeId.Create("coefficient-of-hassum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.coefficient_of_hasSum"),
                H("Taylor coefficient of a convergent scalar series"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At positive radius R, a summable family of coefficient norms weighted by R to the degree and local pointwise convergence to F identify every ordinary Taylor coefficient of F with its series coefficient."))),
                DescribeRole.Theorem),
            Paragraph(Text("The flags l and k label the native legs, with false on the left and true on the right. "
                + "The independent flags e and f label the signed external modes, with true denoting the positive label. "
                + "Write P for the Euler slit period and C(r) for its period correction. The radial variable w gives r = w².")),
            Describe.Lean(DescribeId.Create("original-fourm-signed-tagged-mode"),
                DeclarationHandle.Create(Prefix + "taggedMode"),
                H("Tagging an external mode by its leg"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any label type X, taggedMode places x in the left summand of X ⊕ X "
                    + "when right is false and in the right summand when right is true."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-signed-covariance-mode"),
                DeclarationHandle.Create(Prefix + "covarianceMode"),
                H("Signed covariance generator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At complex u, v and r, equal legs use candidateJ(e,f,u,v,r) plus "
                    + "the Cauchy free term when e ≠ f. Unequal legs use −candidateT(e,f,u,v,r) in either order."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-signed-native-covariance-sum"),
                DeclarationHandle.Create(Prefix + "native_covariance_hasSum"),
                H("Bivariate sum of the actual covariance entries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any lattice data D, colors i and j and flags l, k, e and f, "
                    + "assume ‖u‖ + ‖w‖ < 1 and ‖v‖ + ‖w‖ < 1. The sum over natural modes p and q of "
                    + "the actual effective kernel entry with tagged labels (e,i,p) and (f,j,q), "
                    + "weighted by u^p v^q, is gramComplex(D,i,j) times covarianceMode(l,k,e,f,u,v,w²)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-native-tagged-entry"),
                DeclarationHandle.Create(Prefix + "native_tagged_entry"),
                H("Native Taylor extraction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If ‖w‖ < 1, any two tagged labels recover their actual effective kernel entry "
                    + "by taking the u coefficient at the first mode index and then the v coefficient at the second "
                    + "mode index of the Gram-weighted covariance generator at r = w². The label type is arbitrary "
                    + "and repeated labels and both crossed leg orders are allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-native-mean"),
                DeclarationHandle.Create(Prefix + "native_mean"),
                H("Actual mean in a fixed signed mode"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any lattice charge a and finite external label type with decidable equality, "
                    + "take a label of sign e, color i and mode p at ‖w‖ < 1. Its actual mean is the bilinear pairing "
                    + "of the unit color charge with a times sourceAmplitude(e,p,w²)/period(w²), multiplied by "
                    + "−1 on the left leg and +1 on the right."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-native-spatial-overlap"),
                DeclarationHandle.Create(Prefix + "native_spatial_overlap"),
                H("Native covariance as a corrected spatial kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On ‖u‖ + ‖w‖ < 1 and ‖v‖ + ‖w‖ < 1 with u, v and G(e,f,u,v) nonzero, "
                    + "set r = w² and m = sourceMode(e,u,r) sourceMode(f,v,r). On either equal leg, the generator "
                    + "is m times spatialKernel at parameter 1−r and coordinates rightChart(e,u), rightChart(f,v), "
                    + "with C(r) subtracted inside that product and the Cauchy term subtracted only for e = f. "
                    + "For either unequal-leg order it is −m times the corrected kernel at rightChart(e,u), leftChart(f,r,v)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-native-diagonal"),
                DeclarationHandle.Create(Prefix + "native_diagonal"),
                H("Finite native diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either leg l and sign e, with ‖u‖ + ‖w‖ < 1, "
                    + "covarianceMode(l,l,e,e,·,·,r) tends at (u,u) to "
                    + "(r/4−C(r))/(b(u)h(e,u,r)) + r²u/(8(b(u)h(e,u,r))²), where r = w². "
                    + "The ordinary neighborhood limit includes u = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-leg-sign"),
                DeclarationHandle.Create(Prefix + "legSign"),
                H("Orientation sign of a native leg"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex source orientation is +1 on the left leg and −1 on the right."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-signed-half-source"),
                DeclarationHandle.Create(Prefix + "signedHalfSource"),
                H("Oriented half-coordinate source"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For leg right and mode sign e, the oriented source at complex u and r "
                    + "is legSign(right) times sourceMode(e,u,r)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-signed-native-mean-sum"),
                DeclarationHandle.Create(Prefix + "native_mean_hasSum"),
                H("Sum of the actual mode means"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any lattice data D, charge a, color i and flags l and e, "
                    + "assume ‖u‖ + ‖w‖ < 1. Summing the actual tagged means of the singleton labels (e,i,p) "
                    + "against uᵖ gives the negative bilinear pairing of the unit color charge with a "
                    + "times signedHalfSource(l,e,u,w²)/P(w²)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-half-coordinate-pullback"),
                DeclarationHandle.Create(Prefix + "half_coordinate_pullback"),
                H("Pullback of the elliptic differential"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either leg and either sign, take nonzero complex q and r with "
                    + "‖q²‖ + ‖r‖ < 1. The native lift (x(q),y(q)) satisfies y² = x(x−1)(x−(1−r)) "
                    + "and y ≠ 0. Its x derivative at q is 2y times signedHalfSource(right,e,q²,r), "
                    + "so the source is the coefficient of the pullback of dx/(2y)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-native-geometric-covariance"),
                DeclarationHandle.Create(Prefix + "native_geometric_covariance"),
                H("Restored covariance on the native elliptic chart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any l, k, e and f, set u = q², v = Q² and r = w². Assume "
                        + "‖u‖ + ‖w‖ < 1 and ‖v‖ + ‖w‖ < 1, with q, Q, w and G(e,f,u,v) nonzero. "
                        + "Write x₀ = rightChart(e,u), X₀ = rightChart(f,v) and X₁ = leftChart(f,r,v). "
                        + "Require x₀−1, X₀−1, x₀−X₀ and x₀−X₁ to be nonzero.")),
                    Paragraph(Text("Adding the Cauchy term only when l = k and e = f gives the corrected "
                        + "spatial kernel at the two actual native lift coordinates and parameter 1−r, "
                        + "multiplied by the two oriented sources signedHalfSource(l,e,u,r) and "
                        + "signedHalfSource(k,f,v,r)."))),
                DescribeRole.Theorem))));
}
