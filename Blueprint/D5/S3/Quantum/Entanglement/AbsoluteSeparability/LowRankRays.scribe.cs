using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class LowRankRaysDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/vidaltarrach1999robustness");
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(F.Id(name), [.. xs]);
    private static Formula Par(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula Pow(Formula f, byte n) => new Formula.Power(f, F.D(n));
    private static Formula Rank(Formula f) => Call("R", f);
    private static Formula C => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula N => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Fin(Formula f) => Call("Fin", f);
    private static Formula All(string s, Formula t, Formula b) =>
        F.Seq(F.Forall, F.Sp, Par(F.Seq(F.Id(s), F.Colon, t)), F.Comma, F.Sp, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The identity plus twice a normalized bipartite rank-one projector is a finite sum of positive semidefinite Kronecker products.",
        H("Low-rank separable rays"), Blocks(
            Paragraph(Text("Write R_x = xx* and let the separable cone consist of finite sums of Kronecker products of positive semidefinite matrices. For every complex vector on Fin m times Fin n with sum of squared coordinate norms one, the matrix I + 2 R_x belongs to this cone. The conclusion includes all finite dimensions; the normalization cannot hold when either index set is empty.")),
            Describe.Lean(DescribeId.Create("identity-plus-twice-rank-one-is-separable"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays.separableCone_one_add_two_rankOne"),
                H("A normalized rank-one ray"), StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Vidal--Tarrach Eq. (41), printed page 15, gives random robustness mn a₁a₂ for a normalized pure state with largest Schmidt coefficients a₁,a₂. Since 2a₁a₂ ≤ a₁ squared + a₂ squared ≤ 1, the matrix R_x + one half I is separable. The formal statement is the consequence scaled by two, I + 2 R_x, in the finite-sum separable cone.")),
                    Paragraph(Text("Compactness of the two unit spheres provides a product pair u,v maximizing the real overlap with the vector. If alpha is the maximal overlap and lambda = alpha squared, the two partial contractions equal alpha u and alpha v. The same maximum bounds the reduced matrix by lambda I.")),
                    Paragraph(Text("When lambda is at most one half, twice the finite product-vector average represents 2 R_x plus a reduced-matrix term. The remaining factor I - 2 rho is positive semidefinite.")),
                    Paragraph(Text("When lambda is at least one half, subtract alpha u tensor v to obtain chi, orthogonal to both selected factors. Put U = R_u, V = R_v, P = I - U and Q = I - V. The squared norm of chi is 1 - lambda, and compression of the Gram bound proves K = (1 - lambda) Q - rho_chi positive semidefinite. The projected finite average is corrected by U tensor (V + Q - 4 lambda rho_chi) and P tensor (Q - 2 rho_chi). The correction factors equal V + (2 lambda - 1) squared Q + 4 lambda K and (2 lambda - 1) Q + 2 K, respectively.")),
                    Paragraph(Text("Every averaged vector is a product vector. The proof uses finite moments and compactness, without a Schmidt decomposition. Separability here is the algebraic cone property of finite matrices."))), DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var psi = F.Id("psi");
        var ij = F.Id("ij");
        var domain = F.Seq(Fin(F.Id("m")), F.Times, F.Sp, Fin(F.Id("n")));
        var norm = F.Seq(F.Vert, F.Vert, Call("psi", ij), F.Vert, F.Vert);
        var sum = F.Seq(new Formula.Subscript(F.Sum, F.Seq(ij, F.InMacro, F.Sp, domain)),
            F.Sp, Pow(norm, 2), F.Eq, F.D(1));
        var conclusion = Call("separableCone", F.Seq(F.Id("I"), F.Plus,
            F.D(2), F.Cdot, F.Sp, Rank(psi)));
        var body = All("psi", F.Seq(Par(domain), F.To, F.Sp, C),
            F.Seq(Par(sum), F.Rightarrow, F.Sp, conclusion));
        return All("m", N, All("n", N, body));
    }
}
