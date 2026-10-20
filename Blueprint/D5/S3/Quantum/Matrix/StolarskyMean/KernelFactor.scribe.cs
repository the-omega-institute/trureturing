using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.StolarskyMean;

internal sealed class KernelFactorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/StolarskyMean/KernelFactor";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Stolarsky curvature defect is a product of positive definite functions.",
        H("Positive definiteness of the Stolarsky curvature"), Blocks(
            Describe.Lean(DescribeId.Create("stolarsky-positive-definite-factor-product"),
                DeclarationHandle.Create(Module + ".factor_positiveDefinite"),
                H("The density and quadratic deficit factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Fourier/kosaki2014strong")),
                Blocks(Paragraph(Text("For every real p at least one, put E(a,t)=sinh(at)/(at), continuously extended by one at zero, q=2-1/p, rho=E(p,t) squared divided by E(p+1,t) to the power q and E(1,t) to the power 1/p, and phi=(E(1,t)/E(p,t)) squared. The function factor is rho times E(1,t) to the power minus two times the continuous quadratic deficit of phi, divided by p+1.")),
                    Paragraph(Text("The logarithmic integral formula for E and the Levy density criterion give positive definiteness of rho, of E(1,t) to the power minus two, and of phi. Convexity of the exponential gives h(b,s) at least (b/a)h(a,s) when zero is less than a and a is at most b. Thus q h(p+1,s)+h(1,s)/p-2h(p,s) is nonnegative. All density combinations have the required integrability. Analytic divided slopes establish smoothness at zero. The even smooth phi has a positive definite quadratic deficit by the general second difference theorem, and the Schur product theorem completes the product."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stolarsky-smooth-exponential-profile"),
                DeclarationHandle.Create(Module + ".psi_contDiff"),
                H("Smoothness across the diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real parameter gamma at least two, the exponential Stolarsky profile is continuously differentiable to any prescribed order. It equals (E(gamma,t)/E(1,t)) to the power 1/(gamma-1) on the whole real line. The normalized sinh functions are analytic divided slopes at zero and ordinary smooth quotients elsewhere; their strict positivity makes the real power smooth."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stolarsky-curvature-factorization"),
                DeclarationHandle.Create(Module + ".f_eq_factor"),
                H("The exact curvature factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real gamma at least two, the second derivative of psi(gamma,t)=S(gamma,exp(-t),exp(t)) minus psi equals factor(gamma-1,t) on the whole real line. Away from zero, logarithmic differentiation expresses the derivative defect through coth and inverse sinh squared. The sinh subtraction identity and cosh squared minus sinh squared equals one reduce this expression to the product. In particular rho(p,t)=psi(p+1,t)(E(p,t)/E(p+1,t)) squared.")),
                    Paragraph(Text("The profile is smooth because it equals (E(gamma,t)/E(1,t)) to the power 1/(gamma-1), with a strictly positive base. The quadratic deficit is a compact integral of the continuous second derivative of phi. Both sides of the factorization are therefore continuous, and equality off zero extends to zero. This includes the arithmetic boundary gamma=2 without an extra hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stolarsky-curvature-positive-definite"),
                DeclarationHandle.Create(Module + ".positiveDefinite_f"),
                H("Positive definiteness for every real parameter at least two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real gamma at least two, the complex cast of psi double prime minus psi is positive definite in the existing finite translation Gram definition. The exact factorization identifies it with the preceding positive definite product. This statement allows semidefinite Gram matrices and includes the identically zero defect at gamma=2. It asserts positive definiteness; infinite divisibility of the entire defect is a separate question."))),
                DescribeRole.Theorem))));
}
