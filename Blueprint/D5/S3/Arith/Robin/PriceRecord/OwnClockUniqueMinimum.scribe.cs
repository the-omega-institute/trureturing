using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class OwnClockUniqueMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/OwnClockUniqueMinimum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique real minimum of the actual fixed-support Robin interpolation",
        H("Unique real minimum of the actual fixed-support Robin interpolation"),
        Blocks(
            Paragraph(Text("Assume S is finite and nonempty, every p in S is a distinct natural >=2, and theta_S>1. This module consumes the independently proved compact-sublevel existence and constructed closed-ray fixed point. It operates on exactly OwnClockFixedSupport.phi and realInfimum, retaining EulerGamma, log(log L), and the literal sigma/n Euler factors. OwnClockRobinGap.phi_eq_robin_margin is the existing source provider for the actual natural-grid identification and is neither reproved nor wrapped here. The original objective and real image infimum are imported directly from the existing OwnClockFixedSupport module.")),
            Paragraph(Text("For a true attained minimizer a, vary one supported exponent by t while keeping every other coordinate fixed. The exact derivative is log p*(1/(L log L)-1/(p^(a_p+1)-1)); its benefit part is the existing continuous_prime_hasDerivAt, and its clock part is ordinary composition with the literal finite linear clock. Every t>=1 is feasible. Fermat in the positive tangent direction gives derivative>=0 on the lower face; at a_p>1 the ordinary local-minimum derivative is zero. Solving these conditions with positive denominators gives a_p=max(1,log(1+L log L)/log p-1), retaining C=p^2 as the unique boundary value one. Multiplication by log p and summation gives L=T(L). Every true minimizer therefore has the constructed unique clock Lstar and every coordinate is forced. Because a minimizer already exists, this explicit vector is the minimizer; no KKT sufficiency or affine convexity is assumed.")),
            Paragraph(Text("Supplier audit: HasDerivAt.fun_sum differentiates the finite coordinate sums, Function.update_of_ne fixes every other coordinate, and Function.update_eq_self recovers the original point. The exact imported continuous_prime_hasDerivAt requires p>1 and exponent>=0. For boundary necessity, mem_posTangentConeAt_of_segment_subset supplies direction one in Ici 1; HasDerivAt is restricted to HasDerivWithinAt, converted to HasFDerivWithinAt, and IsLocalMinOn.hasFDerivWithinAt_nonneg gives its sign. IsMinOn.isLocalMin with Ici_mem_nhds supplies the interior Fermat call. Solving KKT pays positive log p, L log L, and p^(a+1)-1 before cross multiplication. Scalar uniqueness consumes both the ray bound and fixed-point equality, with competitor=constructed-clock orientation. The final theorem retains every clause and the exact original sInf; the primary theorem introduces no additional premise.")),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockuniqueminimum-coordinate-hasDerivAt"),
                DeclarationHandle.Create(Prefix + "coordinate_hasDerivAt"), H("The derivative of the literal objective"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each supported p and every admissible finite a, the ambient coordinate derivative of phi S (extend(update a p t)) at t=a_p is w_p*(1/(L log L)-1/(p^(a_p+1)-1)). Both log domains and the actual Euler-factor derivative are paid. This result is consumed by the boundary KKT theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockuniqueminimum-minimizer-kkt"),
                DeclarationHandle.Create(Prefix + "minimizer_kkt"), H("Boundary conditions are consequences of a true minimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every actual minimizer, each displayed derivative is nonnegative, and it is zero whenever a_p>1. The feasible positive tangent cone and ordinary Fermat theorem provide these conclusions, with existence already proved in OwnClockAttainment. The primary theorem assumes none of these conclusions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockuniqueminimum-minimizer-response"),
                DeclarationHandle.Create(Prefix + "minimizer_response"), H("Solving KKT forces the exact exponent vector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual minimizer satisfies a_p=max(1,log(1+L log L)/w_p-1). Interior equality gives p^(a_p+1)=1+L log L. The boundary inequality gives C<=p^2; equality remains a_p=1 and produces no alternate solution."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockuniqueminimum-response-clock-identity"),
                DeclarationHandle.Create(Prefix + "response_clock_identity"), H("The forced coordinate response has its own fixed clock"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive supported logarithmic weights turn the exact coordinate max response into the scalar fixed-point identity. This original supplier is shared by the unique-minimum and residual proofs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockuniqueminimum-unique-real-minimum"),
                DeclarationHandle.Create(Prefix + "unique_real_minimum"), H("General unique actual real minimum and its original infimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is a unique scalar Lstar>=theta with T(Lstar)=Lstar. The vector astar_p=max(1,log(1+Lstar log Lstar)/log p-1) belongs to the original orthant, globally minimizes its literal Phi, and every other genuine finite-coordinate minimizer equals astar. The original realInfimum S equals Phi(astar). There is no prime, cardinality, or 4-card assumption: distinct natural support p>=2 and theta>1 pay the domain directly."))), DescribeRole.Theorem),
            Paragraph(Text("Open endpoints: sign or nonnegativity of this minimum; signed Nicolas baseline and opposite full signed tail; integer optimality or legal integer descent; nonlinear rounding payment, support insertion or support-changing descent; a reduction covering every n>5040; RH. No Fisher/Levi-Civita theorem, all-P>=199 support criterion, P199 finite certificate, official acceptance, freeze, registration or literature novelty is asserted in this delivery. The result remains confined to the stated finite support and real exponent domain.")))));
}
