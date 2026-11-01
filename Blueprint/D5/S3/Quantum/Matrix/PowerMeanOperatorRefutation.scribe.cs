// Uncompiled companion source. No emitted/validated Scribe artifact is claimed.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class PowerMeanOperatorRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact positive definite pair violates the p=2 power-mean distance monotonicity "
        + "in the Euclidean induced operator norm.",
        H("A power-mean counterexample in the Euclidean operator norm"),
        Blocks(
            Paragraph(Text("Version-specific source: Dumitru–Franco, withdrawn v1, Conjecture 9, "
                + "as identified in the supplied independent review. The published 2017 successor "
                + "does not state this exact all-norm assertion. The result here concerns that v1 "
                + "assertion through its p=2 operator-norm specialization; it asserts no novelty, "
                + "priority, or conclusive later-resolution status.")),
            Entry("p2-mean", "mu2", "The p=2 spectral power mean",
                "For complex finite square matrices, mu2 A B t is "
                + "mpow (t • mpow A 2 + (1−t) • mpow B 2) (1/2), using SpectralPower.mpow. "
                + "For positive semidefinite inputs and t in [0,1], it is the positive spectral "
                + "square root of tA²+(1−t)B².", DescribeRole.Definition),
            Entry("specialized-claim", "claim", "Only the p=2 operator-norm specialization",
                "The closed proposition quantifies over every finite dimension n, positive "
                + "semidefinite complex matrices A,B, and real s,t with 0≤s≤t≤1. It requires "
                + "‖A−mu2 A B t‖≤‖A−mu2 A B s‖. The direction is nonincreasing in t. "
                + "Every matrix norm in this statement is Matrix.Norms.L2Operator, the norm "
                + "induced by EuclideanSpace C (Fin n). The full v1 all-norm assertion implies "
                + "this specialization; claim does not encode that full assertion.", DescribeRole.Definition),
            Entry("second-matrix", "X", "The matrix B",
                "X=diag(1/10,4). Its first leading principal minor is 1/10 and its determinant "
                + "is 2/5, so it is positive definite over C.", DescribeRole.Definition),
            Entry("first-matrix", "Y", "The matrix A",
                "Y=[[19/50,−24/25],[−24/25,93/25]]. Its first leading principal minor is "
                + "19/50 and its determinant is 123/250, so it is positive definite over C.",
                DescribeRole.Definition),
            Entry("exact-counterexample", "counterexample", "Exact positive definite witnesses",
                "For A=Y and B=X, the endpoint distance at s=0 is exactly 1, and the distance "
                + "at t=1/100 is strictly greater than 1. Indeed, D=X−Y satisfies D*D=I. "
                + "At t=1/100 the weighted square is S=[[257/12500,−123/3125]," 
                + "[−123/3125,39969/2500]]. Put d=51118101/156250000, T=100051/6250, "
                + "r=√d and w=√(T+2r). Positivity and (S+rI)²=(T+2r)S identify its positive "
                + "spectral root as Q=(S+rI)/w. For the Euclidean unit vector v=(3/5,4/5), "
                + "v*Sv=127521/12500, v*Xv=649/250 and v*Yv=399/250. The exact inequality "
                + "r>57/100 gives (v*Sv+r)/w>649/250, hence v*(Q−Y)v>1. Cauchy–Schwarz "
                + "and the Euclidean induced operator-norm bound give ‖Q−Y‖>1. "
                + "The endpoint uses the positive spectral root of X², namely X. "
                + "An entry maximum, infinity-induced norm, or Frobenius norm is never substituted.",
                DescribeRole.Theorem),
            Entry("specialization-refuted", "result", "The specialized proposition is false",
                "The theorem is literally Not claim, with no additional assumptions. "
                + "The witnesses n=2, A=Y, B=X, s=0, t=1/100 meet the PSD and ordered-parameter "
                + "hypotheses and contradict the required nonincreasing distance. This single "
                + "Euclidean operator norm is unitarily invariant, so the counterexample also "
                + "contradicts the v1 universal all-norm assertion by specialization. "
                + "It does not refute every norm separately or the known p=2 Frobenius statement.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
