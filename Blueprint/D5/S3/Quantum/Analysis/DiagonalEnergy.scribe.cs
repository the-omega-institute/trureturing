using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class DiagonalEnergyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/DiagonalEnergy.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "True bounded resolvents identify the extended state energy of the same diagonal Hamiltonian, while genuine positive-time heat traces retain convergent coefficient sums.",
        H("Resolvent State Energy and Heat Trace"),
        Blocks(
            Definition("resolvent", "The bounded resolvent",
                "For every full complex Hilbert basis e, nonnegative real family h and positive real m, take the actual bounded multiplier with coefficient 1/(m+h(i)) and bound 1/m. The inverse theorem identifies it as the two-sided inverse of the same closed Hamiltonian shifted by m."),
            Definition("resolventVector", "A value in the actual domain",
                "For the same e, h, nonnegativity proof and positive m, every ambient vector x has a resolvent value in the actual domain of hamiltonian e h. Its domain-membership proof comes from the full coefficient graph equation."),
            Definition("capCoeff", "The resolvent cap coefficient",
                "For arbitrary real m and r, capCoeff m r is m*r/(m+r), with Lean real division. The operator constructions use m>0 and r>=0, so the denominator is positive. These scalar coefficients increase with positive m and tend to r along m=n+1."),
            Definition("cap", "The actual bounded energy cap",
                "For every full basis e, nonnegative h and positive m, define the bounded complex linear operator C_m=m*I-m^2*resolvent e h m. Its identities and order properties are derived from the actual resolvent rather than assumed."),
            Definition("stateEnergy", "Extended energy from bounded operator traces",
                "For the same e and nonnegative h, an actual trace-class bounded operator rho and its trace-class proof, take the ENNReal supremum over n of ofReal of the real trace of C_(n+1)*rho. The bounded product is proved trace class. Positivity of rho is an assumption of the energy identification theorem, rather than of this definition. The supremum may be infinite."),
            Result("heat_trace", "Actual trace at every positive time",
                "Let e be any full Hilbert basis of a complete complex Hilbert space and let h(i)>=0 be finite reals. Assume explicitly that exp(-beta*h(i)) is summable for every real beta>0. At every strictly positive nonnegative-real time beta, the actual heat from DiagonalHeat is trace class. Its complex coefficient series has HasSum equal to its literal trace; the real exponential series has HasSum equal to the real part of that trace.",
                "The actual injective range equivalence of e transports the basis to the Set H index required by the analytic trace API. Every basis vector remains a genuine vector of norm one; none is replaced by zero padding. Positivity identifies the absolute-value operator with the heat itself. The genuine summability assumption proves trace class before the general trace-basis formula is used. At zero time no infinite-dimensional trace-class statement is made."),
            Result("resolvent_inverse", "The full actual two-sided inverse",
                "For m>0, R_m is the actual bounded multiplier with coefficients 1/(m+h(i)). Its value R_m x lies in the domain of the same partial-map closure K. The full graph characterization proves K(R_m x)+m*R_m x=x for every ambient x. Conversely, R_m(Ky+m*y)=y for every actual domain vector y. Any bounded operator A whose every value has graph pair (Ax,x-m*Ax) in K equals R_m. The inverse therefore depends on K rather than on an arbitrary coordinate description. These statements include all kernel vectors and require no lower spectral gap."),
            Result("diagonal_resolvent_energy", "Heat, resolvents and extended energy of the same K",
                "Assume the preceding scalar all-temperature summability and let rho be any actual positive trace-class bounded operator. Normalization is unnecessary; noncommutation with K is allowed. The same Hamiltonian has the actual heat trace and both full-domain resolvent identities above. Define C_m=m*I-m^2*R_m as an actual bounded operator. Its literal coefficients are c_m(i)=m*h(i)/(m+h(i)). It is self-adjoint and satisfies 0<=C_m<=m*I in operator order. For every 0<m<=b it satisfies C_m<=C_b in the same operator order, and its stated coefficient formula holds for every ambient vector and index.",
                "The bounded product C_m*rho is genuinely trace class by the two-sided ideal theorem. Its complex coefficient series c_m(i)*inner(e(i),rho e(i)) has HasSum equal to its actual trace. Its real series c_m(i)*Re inner(e(i),rho e(i)) has HasSum equal to the real trace part. The product itself need not be positive. Self-adjointness of C_m moves it to the basis vector inside the inner product; the general trace formula applies without commutation or cyclicity assumptions.",
                "Define the extended state energy by the supremum over n>=0 of ofReal(Re Tr(C_(n+1)*rho)). These actual bounded-trace values increase, and their supremum equals the extended nonnegative sum of ofReal(h(i)*Re inner(e(i),rho e(i))). The coefficients c_(n+1)(i) increase to h(i). Finite-subset sums and their limits give the lower bound for the supremum; c_m(i)<=h(i) gives its upper bound. The identity includes infinite energy and exact zero coefficients. No subtraction of infinity and no undefined unbounded product K*rho is used.",
                "If every h(i)>=1, every actual domain vector x also satisfies norm(x)^2<=Re inner(x,Kx). Finite graph approximants prove the inequality first for algebraic basis sums and then pass both graph coordinates to the limit. This does not assert that the operator domain equals H, nor that finite state energy is the operator-domain condition.",
                "The state energy here is defined by these canonical resolvent approximants of K. Equality to any separate spectral-energy carrier requires its own bridge. The scalar summability hypothesis must be derived by any later original common-Hamiltonian application. No original Shirokov family theorem, common reference, entropy-continuity implication or literature priority is asserted. The imported general trace and ideal proofs retain Tom Ole Diem's PhysLean Apache-2.0 attribution."))));
    private static DocumentBlock.Describe Result(string name, string title, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("diagonal-energy-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()),
            DescribeRole.Theorem);
    private static DocumentBlock.Describe Definition(string name, string title, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("diagonal-energy-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()),
            DescribeRole.Definition);

}
