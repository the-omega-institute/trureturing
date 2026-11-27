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
        Formula defectA = Sub(ss, Mul(Norm(p), alpha));
        Formula defectB = Sub(Mul(Norm(p), alpha), ss);
        Formula compress = Mul(D(2), Add(ss, Mul(alpha, Dot(p, q))));
        Formula triangle = Mul(Mul(D(2), s),
            Add(ss, Mul(alpha, Add(Add(Dot(p, q), Dot(q, r)), Dot(r, p)))));
        Formula holonomy = Mul(Mul(D(2), alpha), Dot(p, Call("mul", q, r)));
        Formula compressLeft = Shell(s, p, Shell(s, q, Shell(s, p, v)));
        Formula triangleLeft = Shell(s, p, Shell(s, q, Shell(s, r, z)));
        Formula onShell = Equal(ss, Mul(Norm(p), alpha));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Shell maps of integer quaternions: two-point compression and the oriented triangle identity.",
            H("Shell compression and the oriented triangle"),
            Blocks(
                Paragraph(Text("For an integer s and quaternions p, a the shell map is P(s, p, a, v) = s v + p v a. Purity of p, q, r and a means that the real coordinate vanishes, and N(x) = x·x is the squared norm. The pair action v ↦ c v + (d v) a composes by the rule obtained from a a = −N(a), which reduces every identity below to an integer polynomial identity in the coordinates of p, q, r, the integer s and the integer N(a).")),
                Law("omega-shell-compress", "shell_compress", "Two-point shell compression",
                    If(Pure(p, q, a), Equal(compressLeft,
                        Add(Mul(compress, z), Mul(defectA, Shell(Neg(s), q, v))))),
                    "No norm condition is assumed. The last term is (s² − N(p)N(a)) (q v a − s v). Each purity hypothesis is needed: a symbolic expansion with a general real coordinate in p, in q or in a gives a nonzero difference."),
                Law("omega-shell-compress-on-shell", "shell_compress_of_eq", "Compression on the shell",
                    If(And(Pure(p, q, a), onShell), Equal(compressLeft, Mul(compress, z))),
                    "When s² = N(p)N(a) the map P(s, p, a, ·) squares to 2s times itself, and the composition through q returns a multiple of the same map. The coefficient 2(s² + N(a)(p·q)) needs no condition on N(q)."),
                Law("omega-shell-triangle", "shell_triangle", "Oriented triangle identity",
                    If(And(Pure(p, q, a), Call("pure", r)), Equal(triangleLeft,
                        Add(Add(Mul(triangle, z), Mul(holonomy, Call("mul", z, a))),
                            Mul(defectB, Shell(Neg(s), r, Shell(Neg(s), q, v)))))),
                    "Here z = P(s, p, a, v). No norm condition is assumed. For pure p, q, r the scalar p·(q r) equals the determinant of the three imaginary coordinate vectors. The defect is (N(p)N(a) − s²) times the composition (s − r · a)(s − q · a) applied to v. Purity of p, q, r and a is each needed by the same symbolic test."),
                Law("omega-shell-triangle-on-shell", "shell_triangle_of_eq", "Triangle identity on the shell",
                    If(And(And(Pure(p, q, a), Call("pure", r)), onShell), Equal(triangleLeft,
                        Add(Mul(triangle, z), Mul(holonomy, Call("mul", z, a))))),
                    "Only s² = N(p)N(a) is used; N(q) and N(r) are arbitrary. With N(p) = N(q) = N(r) = N(a) = R and s = R this reads P_p P_q P_r z = 2R[R(R + p·q + q·r + r·p) z + det(p, q, r) z a]. Over the real numbers P/(2s) is then a rank-one projection of the quaternions viewed as a two-dimensional complex space; that identification is not formalized in this module."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Shell(Formula s, Formula p, Formula v) => Call("P", s, p, F.Id("a"), v);
    private static Formula Norm(Formula x) => Call("N", x);
    private static Formula Dot(Formula x, Formula y) => Call("dot", x, y);
    private static Formula Pure(Formula x, Formula y, Formula z) =>
        And(Call("pure", x), And(Call("pure", y), Call("pure", z)));
    private static Formula Neg(Formula x) => Sub(D(0), x);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula If(Formula left, Formula right) => Disp(new Formula.Logic(left, FormulaLogicOperator.Implies, right));

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string commentary) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))), DescribeRole.Theorem);
}
