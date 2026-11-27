using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaShellExactnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaShellExactness";

    public DocumentDefinition Create()
    {
        Formula s = F.Id("s"), p = F.Id("p"), q = F.Id("q"), r = F.Id("r"), a = F.Id("a");
        Formula v = F.Id("v"), z = Shell(s, p, v), zero = D(0);
        Formula ss = Mul(s, s), alpha = Norm(a);
        Formula compress = Mul(D(2), Add(ss, Mul(alpha, Dot(p, q))));
        Formula triangle = Mul(Mul(D(2), s),
            Add(ss, Mul(alpha, Add(Add(Dot(p, q), Dot(q, r)), Dot(r, p)))));
        Formula holonomy = Mul(Mul(D(2), alpha), Dot(p, Call("mul", q, r)));
        Formula compressLeft = Shell(s, p, Shell(s, q, Shell(s, p, v)));
        Formula triangleLeft = Shell(s, p, Shell(s, q, Shell(s, r, z)));
        Formula onShell = Equal(ss, Mul(Norm(p), alpha));
        Formula compressAll = All("v", Equal(compressLeft, Mul(compress, z)));
        Formula triangleAll = All("v", Equal(triangleLeft,
            Add(Mul(triangle, z), Mul(holonomy, Call("mul", z, a)))));
        Formula compressCases = Or(onShell, And(Equal(s, zero), Equal(q, zero)));
        Formula triangleCases = Or(onShell,
            Or(And(Equal(s, zero), Or(Equal(q, zero), Equal(r, zero))),
                And(Equal(q, new Formula.Negate(r)), Equal(ss, Mul(Norm(r), alpha)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact classifications of the inputs for which the shell compression and triangle identities hold for every v.",
            H("Exactness of the shell compression and triangle identities"),
            Blocks(
                Paragraph(Text("For an integer s and integer quaternions p, a the shell map is P(s, p, a, v) = s v + p v a. Purity means that the real coordinate vanishes and N(x) = x·x is the squared norm. On the shell s² = N(p)N(a) the composition P_p P_q P_p is the multiple 2(s² + N(a) p·q) of P_p, and P_p P_q P_r P_p is 2s(s² + N(a)(p·q + q·r + r·p)) P_p plus 2N(a) p·(q r) times the map v ↦ (P_p v) a. The two theorems below state, for pure p, q, r, a, exactly which inputs make these defect-free identities hold for every quaternion v.")),
                Paragraph(Text("The library proofs are Omega.Quaternion.shell_compress_iff and Omega.Quaternion.shell_triangle_iff in OmegaMath.Algebra.Quaternion.Shell. Both start from the exact identities Omega.Quaternion.shell_compress and Omega.Quaternion.shell_triangle, whose defect terms are (s² − N(p)N(a)) P_{−s,q,a} v and (N(p)N(a) − s²) P_{−s,r,a} P_{−s,q,a} v. For the triangle, the composite P_{−s,r,a} P_{−s,q,a} is the pair action v ↦ c v + (d v) a with c = s² − N(a)(r q) and d = −s(q + r). A pair action that vanishes for every v has c = 0, and d = 0 unless a = 0: evaluating at v = 1 gives c = −d a, and then d (u a − a u) = 0 for u = i, j, k; since integer quaternions have no zero divisors (Omega.Quaternion.eq_zero_or_eq_zero_of_mul_eq_zero, from the multiplicativity of the squared norm), either d = 0 or all three commutators vanish, which for pure a forces a = 0. The case analysis on s = 0 and q + r = 0 then gives the three cases of the classification.")),
                Law("omega-shell-compress-iff", "shell_compress_iff_of_shell", "Exact compression condition",
                    If(Pure(p, q, a), Iff(compressAll, compressCases)),
                    "The degenerate case s = 0, q = 0 is the only way off the shell: then both sides vanish. When a = 0 or p = 0 the shell condition reads s = 0; for a = 0 the identity itself reduces to s³ v = 2 s³ v. Each purity hypothesis is needed for the equivalence. With s = 1 and the other inputs equal to i the shell condition holds, yet replacing q by 1 gives the difference (0, 0, 0, −4) of the two sides at v = j, replacing a by 1 gives (−6, −2, 0, 0) at v = 1, and replacing p by 1 gives (−2, −2, 0, 0) at v = 1; coordinates are listed as (w, x, y, z), and each replacement keeps the right-hand case true and the other hypotheses intact. These counterexamples were computed independently and are not checked by compiled Lean.",
                    AssessedProvenance.FromRepo()),
                Law("omega-shell-triangle-iff", "shell_triangle_iff_of_shell", "Exact triangle condition",
                    If(And(Pure(p, q, a), Call("pure", r)), Iff(triangleAll, triangleCases)),
                    "Here z = P(s, p, a, v). Besides the shell there are two families. If s = 0 and q = 0 or r = 0, the composite P_{−s,r,a} P_{−s,q,a} is zero. If q = −r and s² = N(r)N(a), then d = 0 and c = s² − N(a)N(r) = 0 because r r = −N(r); this family is genuinely off the shell, for instance s = 1, p = 2j, q = −i, r = i, a = i, where N(p)N(a) = 4. Degenerate cases: for a = 0 the identity reads s⁴ v = 2 s⁴ v and all three cases reduce to s = 0; for p = 0 the shell condition is s = 0; for q = 0 or r = 0 the third case is contained in the second, so the condition is s² = N(p)N(a) or s = 0; for s = 0 the condition is that one of p, q, r, a is zero. Each purity hypothesis is needed for the equivalence. With s = 1, q = r = 0 and a = i, the shell condition holds for p = 1 but the difference of the two sides at v = 1 is (−2, 0, 0, 0); with s = 1, p = a = i and r = 0, replacing q by 1 gives the difference (0, 0, 0, −4) at v = j, and the same holds with q = 0 and r replaced by 1; with s = 1, p = i, q = r = 0 and a = 1 the difference at v = 1 is (−2, 0, 0, 0). In each example the shell condition holds and the remaining hypotheses are intact, so the right-hand side is true while the identity fails. These counterexamples were computed independently and are not checked by compiled Lean.",
                    AssessedProvenance.FromRepo()))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Shell(Formula s, Formula p, Formula v) => Call("P", s, p, F.Id("a"), v);
    private static Formula Norm(Formula x) => Call("N", x);
    private static Formula Dot(Formula x, Formula y) => Call("dot", x, y);
    private static Formula Pure(Formula x, Formula y, Formula z) =>
        And(Call("pure", x), And(Call("pure", y), Call("pure", z)));
    private static Formula All(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), F.Id("Quaternion"), body);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula If(Formula left, Formula right) => Disp(new Formula.Logic(left, FormulaLogicOperator.Implies, right));

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement,
        string commentary, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"), H(title),
            StatementSource.FromAuthor(statement), provenance,
            Blocks(Paragraph(Text(commentary))), DescribeRole.Theorem);
}
