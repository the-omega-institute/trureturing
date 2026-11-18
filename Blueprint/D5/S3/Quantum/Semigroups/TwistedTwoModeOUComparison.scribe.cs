using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class TwistedTwoModeOUComparisonDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Index => C("Prod", C("Fin", D(2)), C("Fin", D(2)));
    private static Formula Psi => V("psi");
    private static Formula Q => V("q");
    private static Formula Space => C("EuclideanSpace", Complex, Index);
    private static Formula At(byte a, byte b) => C("at", Psi, C("pair", D(a), D(b)));
    private static Formula N(Formula a) => C("normSq", a);
    private static Formula Add(Formula a, Formula b) => C("add", a, b);
    private static Formula Mul(Formula a, Formula b) => C("mul", a, b);
    private static Formula Sub(Formula a, Formula b) => C("sub", a, b);
    private static Formula Sq(Formula a) => C("pow", a, D(2));
    private static Formula H(byte i, Formula x) => C("jumpMap", C("modeJump", D(i)), Q, x);
    private static DocumentBlock Entry(string id, string name, string title, Formula statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name),
            DefinitionDsl.H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create()
    {
        Formula j = C("matrix", D(0), D(1), D(0), D(0));
        Formula z = C("diagonal", C("pair", C("neg", D(1)), D(1)));
        Formula u = C("ofLp", Psi), pure = C("vecMulVec", u, C("star", u));
        Formula budget = Add(Add(Sq(Add(N(At(0,0)), N(At(0,1)))), Sq(Add(N(At(0,0)), N(At(1,0))))),
            Add(Mul(D(2), N(Mul(At(0,0), At(1,1)))), Mul(D(2), N(Mul(At(0,1), At(1,0))))));
        Formula rhs = Sub(D(1), C("div", Mul(Mul(Q, Sub(D(1), Q)), C("directionalBudget", Psi)), D(2)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The two literal Jordan-Wigner Kraus maps attenuate every complex unit pure state by a quartic budget.",
            DefinitionDsl.H("Two-mode pure-state attenuation"), Blocks(
                Paragraph(Text("Use the ordered basis 00,01,10,11. J is [[0,1],[0,0]] and Z is diag(-1,1). The modes are J tensor I and Z tensor J. Each H is the unital completely positive jumpMap from TwoKrausRankOneAttenuation, without a trace-preservation claim. All matrix, PSD and L2 operator norm carriers are the existing ones.")),
                Entry("modes", "modeJump", "Literal fermionic modes",
                    All("i", C("Fin", D(2)), Eq(C("modeJump", V("i")), C("at", C("pair", C("kronecker", j, D(1)), C("kronecker", z, j)), V("i")))),
                    "Both modes satisfy J_i squared=0 and J_i J_i*+J_i* J_i=I. The literal twist W=diag(1,1,-1,1) sends I tensor J to minus Z tensor J; the overall minus cancels in the Kraus sandwich. The proved bound uses the displayed modes directly and does not assert a separate twist-conjugation theorem.", DescribeRole.Definition),
                Entry("budget", "directionalBudget", "Actual directional budget",
                    All("psi", Space, Eq(C("directionalBudget", Psi), budget)),
                    "Write p1=|c00|²+|c01|² and p2=|c00|²+|c10|². This is exactly V=p1²+p2²+2|c00 c11|²+2|c01 c10|². For a unit vector it also equals 2|c00|²+(|c01|²+|c10|²)². No real-phase restriction is imposed.", DescribeRole.Definition),
                Entry("pure-state-loss", "two_mode_pure_state_attenuation", "Both-mode attenuation",
                    All("q", Real, Imp(Le(D(0), Q), Imp(Le(Q, D(1)), All("psi", Space, Imp(Eq(C("norm", Psi), D(1)),
                        Le(C("opNorm", H(0, H(1, pure))), rhs)))))),
                    "For each mode the generic theorem bounds norm(H_i(P)) by 1−q(1−q)(p_i−|c_i|²). Entrywise complex algebra and unit normalization prove the sum of these two defects is V. The two actual maps commute; positivity and unital Hermitian contraction therefore bound norm(H1(H2(P))) by each single-mode norm. Averaging yields the stated factor one half. opNorm means norm of Matrix.toEuclideanCLM. Parameter endpoints and arbitrary complex phases are included. The filtered no-jump estimate, full low-temperature tube and nonnegativity of G are not claimed here.", DescribeRole.Theorem))));
    }
}
