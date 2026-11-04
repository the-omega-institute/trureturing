using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ReplicaThreeCurveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The labelled B=C=b curve has A=N-2b and positive scalar domain 0<b<N/2. Its derivative has the sign of b-N/3, its continuous minimum is uniquely N/3, and its two scalar endpoint limits are zero. Physical sizes additionally must be positive integers.",
        H("The labelled equal-party curve and its boundaries"),
        Blocks(
            Paragraph(Text("Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0; Camargo and Nishida for the fully symmetric pure Gaussian family and equal-party observation. Size dependence here is not a dynamical evaporation theorem. The source's real scalar interpolation does not assert fractional physical modes.")),
            Node("curve", "The scalar B=C curve", "curve", "F",
                "F(k,N,b)=V(k,N-2b,b,b). For k>0 and N>0 its positive scalar domain is 0<b<N/2. For actual fixed integer total N>=3 and squeezing a>1, use k=kappa(N,a).", DescribeRole.Definition),
            Node("coefficient", "The exact derivative coefficient", "curveDerivative", "F'",
                "Put A=N-2b, M=1+k(2Nb-3b^2), L=1+2kb(N-2b), R=1+kb(N-b). The exact coefficient is k^2 b(3b-N)[N+k(2A^2 b+3Ab^2+2b^3)]/(6LRM). In the positive scalar domain every factor except 3b-N is strictly positive.", DescribeRole.Definition),
            Node("derivative", "Derivative and all three signs", "curve_derivative", "F'",
                "For every k>0,N>0 and 0<b<N/2, F is differentiable at b with the exact curveDerivative coefficient. Its derivative is negative if and only if b<N/3, zero if and only if b=N/3, and positive if and only if N/3<b.", DescribeRole.Theorem),
            Node("minimum", "The unique continuous minimum", "curve_minimum", "F",
                "For k>0,N>0, F is strictly decreasing on (0,N/3] and strictly increasing on [N/3,N/2). At every b in (0,N/2), F(N/3)<=F(b), with equality if and only if b=N/3. The theorem proves both sides of the unique global minimum across the full scalar interval.", DescribeRole.Theorem),
            Node("boundaries", "Scalar endpoints and vacuum", "curve_boundaries", "F",
                "For k>=0,N>0, F(k,N,0)=F(k,N,N/2)=0, with right limit zero at 0 and left limit zero at N/2. At k=0 the whole real curve is identically zero. Empty-party endpoints lie outside the three-positive-party physical theorem. No false strict vacuum derivative is asserted.", DescribeRole.Theorem),
            Node("physical", "The divisible-total physical curve", "physical_curve_minimum", "GM",
                "For every integer N>=3 divisible by 3, a>1, positive integer b with 2b<N, the actual GM3 3 (N-2b) b b a equals F(kappa(N,a),N,b). Its value is at least the actual equal-party value at (N/3,N/3,N/3), with equality if and only if b=N/3. Equivalently the multi-entropy subsystem B+C has size 2N/3. These are positive integer physical modes. For other residues the scalar continuous minimum remains valid, while no fractional-mode physical minimizer is asserted. At vacuum all admissible curve points tie by the physical vacuum theorem.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string symbol, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gaussian-three-curve-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(F.Id(symbol))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, null);
}
