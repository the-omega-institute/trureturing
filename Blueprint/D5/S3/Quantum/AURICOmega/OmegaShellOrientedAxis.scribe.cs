using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaShellOrientedAxisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaShellOrientedAxis";

    public DocumentDefinition Create()
    {
        Formula p = F.Id("p"), q = F.Id("q"), r = F.Id("r"), a = F.Id("a"), x = F.Id("x");
        Formula forward = Add(Add(U(p, U(q, U(r, x))), U(q, U(r, U(p, x)))), U(r, U(p, U(q, x))));
        Formula reverse = Add(Add(U(p, U(r, U(q, x))), U(r, U(q, U(p, x)))), U(q, U(p, U(r, x))));
        Formula coefficient = Mul(Mul(D(6), Norm(a)), Dot(p, Call("mul", q, r)));
        Formula pure = And(And(Call("pure", p), Call("pure", q)), And(Call("pure", r), Call("pure", a)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The oriented axis identity for the integer quaternion maps v ↦ (c v) a with pure c and a.",
            H("The oriented axis of three quaternion maps"),
            Blocks(
                Paragraph(Text("For integer quaternions c and a write u(c, v) = (c v) a; u(c, ·) is the part v ↦ c v a that the shell map P(s, c, a, v) = s v + c v a adds to the multiple s v. Purity means that the real coordinate vanishes, N(a) = a·a is the squared norm, and for pure p, q, r the scalar p·(q r) is the determinant of their imaginary coordinate vectors. The theorem below takes the three compositions u_p u_q u_r, u_q u_r u_p, u_r u_p u_q in cyclic order and subtracts the three compositions in reverse order; the result is the multiple 6 N(a) (p·(q r)) of the single map x ↦ x a. No shell condition and no integer s enter.")),
                Paragraph(Text("The library proof is Omega.Quaternion.oriented_axis in OmegaMath.Algebra.Quaternion.Shell. It is derived from the general form Omega.Quaternion.oriented_axis_general in the same module, which assumes only that a is pure and allows arbitrary p, q, r, x: the left side equals −N(a) (A x) a, where A = pqr + qrp + rpq − prq − rqp − qpr is the alternating sum of the six ordered products. That step uses associativity and a a = −N(a). For pure p, q, r the alternating sum is the scalar −6 p·(q r), which is certified as an integer polynomial identity in the coordinates of p, q, r.")),
                Law("omega-shell-oriented-axis", "oriented_axis_from_shell", "Oriented axis identity",
                    If(pure, Equal(new Formula.Binary(forward, FormulaBinaryOperator.Subtract, reverse),
                        Mul(coefficient, Call("mul", x, a)))),
                    "The identity holds for every quaternion x; x need not be pure. With p = i, q = j, r = k and a = i, where N(a) = 1 and p·(q r) = 1, it reads 6 x i. Relative to the stated right side 6 N(a) (p·(q r)) (x a), each of the four purity hypotheses is needed. Keep x = 1 and the other inputs as above, and list the difference of the left side minus the right side in coordinates (w, x, y, z): replacing p by 1 gives (2, 0, 0, 0), replacing q by 1 gives (0, 0, 0, 2), replacing r by 1 gives (0, 0, −2, 0), and replacing a by 1 gives (−12, 0, 0, 0). Each replacement keeps the other three hypotheses true, so no proper subset of the four hypotheses suffices. For arbitrary p, q, r the general picture is Omega.Quaternion.oriented_axis_general: the left side is −N(a) (A x) a. Writing w_c for the real coordinate of c, [c, d] = c d − d c for the commutator and det(p⃗, q⃗, r⃗) for the determinant of the imaginary coordinate vectors, the alternating sum has the closed form A = −6 det(p⃗, q⃗, r⃗) + w_p [q, r] + w_q [r, p] + w_r [p, q]. For every integer quaternion a, a³ = −N(a) a holds exactly when a is pure. The antisymmetrised triple product is classical; no repository note states this integer identity. The counterexamples, the closed form for A and the characterisation of a³ were computed independently by symbolic expansion and are not checked by compiled Lean.",
                    AssessedProvenance.FromRepo()))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula U(Formula c, Formula v) => Call("u", c, F.Id("a"), v);
    private static Formula Norm(Formula x) => Call("N", x);
    private static Formula Dot(Formula x, Formula y) => Call("dot", x, y);
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
