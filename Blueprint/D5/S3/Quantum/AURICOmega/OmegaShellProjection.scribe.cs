using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaShellProjectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaShellProjection";

    public DocumentDefinition Create()
    {
        Formula s = F.Id("s"), p = F.Id("p"), q = F.Id("q"), r = F.Id("r"), a = F.Id("a");
        Formula v = F.Id("v"), z = Shell(s, p, v);
        Formula ss = Mul(s, s), alpha = Norm(a);
        Formula compress = Mul(D(2), Add(ss, Mul(alpha, Dot(p, q))));
        Formula triangle = Mul(Mul(D(2), s),
            Add(ss, Mul(alpha, Add(Add(Dot(p, q), Dot(q, r)), Dot(r, p)))));
        Formula holonomy = Mul(Mul(D(2), alpha), Dot(p, Call("mul", q, r)));
        Formula compressLeft = Shell(s, p, Shell(s, q, Shell(s, p, v)));
        Formula triangleLeft = Shell(s, p, Shell(s, q, Shell(s, r, z)));
        Formula onShell = Equal(ss, Mul(Norm(p), alpha));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Two on-shell identities for integer quaternion shell maps: two-point compression and the oriented triangle.",
            H("Shell compression and the oriented triangle"),
            Blocks(
                Paragraph(Text("For an integer s and quaternions p, a the shell map is P(s, p, a, v) = s v + p v a. Purity of p, q, r and a means that the real coordinate vanishes, and N(x) = x·x is the squared norm. Both identities below assume the shell condition s² = N(p)N(a). The general forms without that condition, each with an explicit defect term proportional to s² − N(p)N(a), are Omega.Quaternion.shell_compress and Omega.Quaternion.shell_triangle in OmegaMath.Algebra.Quaternion.Shell; their proofs rewrite every shell map as a pair action v ↦ c v + (d v) a, compose pair actions using a a = −N(a), and certify the resulting integer polynomial identity in s, N(a) and the coordinates of p, q, r.")),
                Paragraph(Text("Over the real numbers, when s ≠ 0 and s² = N(p)N(a), the map P/(2s) on the quaternions viewed as ℂ² is the rank-one qubit projection (1 + p̂·σ)/2, where p̂ is the unit vector of p. In that reading the compression identity is the integer rescaling of P_a P_b P_a = Tr(P_a P_b) P_a for rank-one projections, and the triangle identity is the integer rescaling of the three-state Bargmann invariant ⟨a|b⟩⟨b|c⟩⟨c|a⟩ = (1 + a·b + b·c + c·a + i det(a, b, c))/4 that defines the Pancharatnam phase. Neither the identification with projections nor these real or complex formulas is formalized in this module. The real and complex Bloch-vector form of the three-state invariant is the separate theorem D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.triple_bargmann_bloch; this module states the integer quaternion identity and does not depend on it.")),
                Law("omega-shell-compress-on-shell", "shell_compress_of_eq", "Compression on the shell",
                    If(And(Pure(p, q, a), onShell), Equal(compressLeft, Mul(compress, z))),
                    "On the shell, P(s, p, a, ·) squares to 2s times itself and the composition through q returns a multiple of the same map; no condition on N(q) is used. The shell condition cannot be dropped: for s = 0, p = i, q = j, a = i and v = 1 the left side is k and the right side is 0. It is also not necessary: the library theorem Omega.Quaternion.shell_compress_iff states that, for pure p, q, a, the identity holds for every v exactly when s² = N(p)N(a), or s = 0 and q = 0. Each purity hypothesis is needed. With s = 1 and the other inputs equal to i, replacing q by 1 gives the difference (0, 0, 0, −4) at v = j, replacing a by 1 gives (−6, −2, 0, 0) at v = 1, and replacing p by 1 gives (−2, −2, 0, 0) at v = 1; coordinates are listed as (w, x, y, z), and each choice satisfies the shell condition. These counterexamples were computed independently and are not checked by compiled Lean.",
                    AssessedProvenance.FromRepo()),
                Law("omega-shell-triangle-on-shell", "shell_triangle_of_eq", "Triangle identity on the shell",
                    If(And(And(Pure(p, q, a), Call("pure", r)), onShell), Equal(triangleLeft,
                        Add(Mul(triangle, z), Mul(holonomy, Call("mul", z, a))))),
                    "Here z = P(s, p, a, v), and for pure p, q, r the scalar p·(q r) equals the determinant of the three imaginary coordinate vectors. Only s² = N(p)N(a) is used; N(q) and N(r) are arbitrary. With N(p) = N(q) = N(r) = N(a) = R and s = R it reads P_p P_q P_r z = 2R[R(R + p·q + q·r + r·p) z + det(p, q, r) z a]. The shell condition cannot be dropped: for s = 0, p = i, q = j, r = k, a = i and v = 1 the difference of the two sides is (0, 1, 0, 0). Each purity hypothesis is needed. With s = 1 and the other inputs equal to i, replacing r by 1 or q by 1 gives the difference (0, 0, 0, −4) at v = j, replacing p by 1 gives (−6, −2, 0, 0) at v = 1, and replacing a by 1 gives (−12, −8, 0, 0) at v = 1. These counterexamples were computed independently and are not checked by compiled Lean. The converse direction, for which inputs the triangle identity holds for every v, is not examined. The cited notes give the Bargmann invariant as a cyclic product of overlaps and the Pancharatnam phase of a closed sequence of states; they do not state this integer identity, which is derived here.",
                    AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/HilbertOperators/oszmaniec2021relational"),
                        LibraryNoteRef.Create("D5/L/HilbertOperators/pancharatnam1956interference"))))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Shell(Formula s, Formula p, Formula v) => Call("P", s, p, F.Id("a"), v);
    private static Formula Norm(Formula x) => Call("N", x);
    private static Formula Dot(Formula x, Formula y) => Call("dot", x, y);
    private static Formula Pure(Formula x, Formula y, Formula z) =>
        And(Call("pure", x), And(Call("pure", y), Call("pure", z)));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula If(Formula left, Formula right) => Disp(new Formula.Logic(left, FormulaLogicOperator.Implies, right));

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement,
        string commentary, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"), H(title),
            StatementSource.FromAuthor(statement), provenance,
            Blocks(Paragraph(Text(commentary))), DescribeRole.Theorem);
}
