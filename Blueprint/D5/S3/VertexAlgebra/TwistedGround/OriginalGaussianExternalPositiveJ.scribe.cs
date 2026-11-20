using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalPositiveJDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalPositiveJ.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spatial regularity and positive J equality for the original Gaussian kernel",
        H("The original Hilbert mode sums and the positive J equation"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-gaussian-external-joint-differentiable"),
                DeclarationHandle.Create(Prefix + "kernelMode_joint_differentiable"),
                H("Joint spatial differentiability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any Booleans square, out and out′ and complex u, v and z with "
                        + "‖u‖ + ‖z‖ < 1 and ‖v‖ + ‖z‖ < 1, the original kernelMode is complex Fréchet "
                        + "differentiable at (u,v) jointly in its two external coordinates with z fixed. "
                        + "The flag square selects T when true and J when false.")),
                    Paragraph(Text("For either sign ε, let Xε(w,z) = ∑ₙ wⁿ • externalVector(ε,n,z) in the original "
                        + "Hilbert space H, where the sum is over the natural numbers. For each w in the convergence disk, "
                        + "choose a radius ρ with ‖w‖ < ρ < 1 − ‖z‖. The norms of the terms at ρ form a summable "
                        + "majorant throughout the open disk of radius ρ. Local normal convergence of the vector "
                        + "polynomials gives complex differentiability of each Hilbert-valued sum.")),
                    Paragraph(Text("The kernel is the continuous complex bilinear pairing of Xout(u,z) with "
                        + "A(z) applied to Xout′(v,z), where A(z) is the square resolvent for T and the odd "
                        + "resolvent for J. Passing the two sums through the continuous linear maps in the pairing "
                        + "recovers the original mode coefficients by the explicit contraction identities. "
                        + "Absolute summability identifies the iterated sum with the joint sum over ℕ × ℕ. "
                        + "The bilinear chain rule gives the joint derivative, and the strict inequalities ensure "
                        + "the factorization holds on a neighborhood of (u,v)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-gaussian-external-positive-j-equality"),
                DeclarationHandle.Create(Prefix + "positiveJ_eq_candidateJ"),
                H("Native positive J kernel equality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For real r with 0 < r < 1 and complex u and v with "
                        + "‖u‖ + √r < 1 and ‖v‖ + √r < 1, "
                        + "kernelMode(false, true, true, u, v, (√r : ℂ)) = candidateJ(u, v, (r : ℂ)). "
                        + "These hypotheses include the diagonal and zero external coordinates.")),
                    Paragraph(Text("For fixed r, let F be the original positive J kernel minus the regular "
                        + "candidate on the bidisk of radius 1 − √r. The inequality r ≤ √r places that bidisk "
                        + "inside the candidate's spatial domain, where nonvanishing of its W sum gives joint "
                        + "analyticity. The literal kernel is jointly differentiable by the Hilbert mode factorization. "
                        + "Subtracting the candidate equation from the literal displacement equation cancels the "
                        + "common source and the constant 1/4. The difference satisfies "
                        + "a(1−a) ∂₁F(a,b) + b(1−b) ∂₂F(a,b) + (1−3(a+b)/2) F(a,b) = 0.")),
                    Paragraph(Text("For real 0 ≤ t ≤ 1, set D_w(t) = 1 − w + tw and φ_w(t) = tw/D_w(t) for "
                        + "w equal to u or v. Both denominators stay nonzero and ‖φ_w(t)‖ ≤ ‖w‖, so the path "
                        + "stays inside the bidisk. Along this path the chain rule and the homogeneous equation "
                        + "give zero derivative for t² F(φ_u(t),φ_v(t))² / (D_u(t)³ D_v(t)³). "
                        + "This expression is constant on [0,1]. Its value is zero at t = 0 and equals "
                        + "F(u,v)² at t = 1, which forces F(u,v) = 0."))),
                DescribeRole.Theorem))));
}
