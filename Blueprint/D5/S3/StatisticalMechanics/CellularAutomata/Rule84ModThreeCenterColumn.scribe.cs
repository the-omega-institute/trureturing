using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class Rule84ModThreeCenterColumnDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/nersissian2026diagonalbases");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical polynomial lift of Rule 84 from a single seed has center column 1 at time zero and the repeating block (1, 2, 2) at every positive time modulo three. A forward-invariant language of length-seven windows proves the pattern for all time.",
        H("The Rule 84 center column modulo three"),
        Blocks(
            Node("orbit", "The canonical single-seed orbit", OrbitFormula(),
                "Definition 1, page 4 of arXiv:2609.25078v1: \"The variables a, b, c are the left, center and right neighbors.\" \"For an initial condition c₀ = (c₀(0), c₀(1), …) placed at x = 0, 1, … on a zero background, write A_{R,c₀}(t, x), t ≥ 0, x ∈ Z, for the orbit under p_R.\" Here R = 84, the modulus is 3, and c₀ is the single seed δ₀. Time t is a natural number, position x is an integer, and all cell values and polynomial arithmetic lie in ZMod 3. The three inputs at time t are A(t, x − 1), A(t, x), A(t, x + 1), respectively. The displayed ite(condition, u, v) equals u when the condition holds and v otherwise; it gives exactly one nonzero cell at time zero.",
                "A", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The outstanding Rule 84 pattern", ClaimFormula(),
                "Remark 6, page 12 of arXiv:2609.25078v1: \"(The outstanding Rule 84 case) The polynomial of Rule 84 is (a + b + ab)(1 + c). Modulo three, its center column begins 1, 1, 2, 2, 1, 2, 2, … and follows the repeating block (1, 2, 2) after the first entry for the tested times 0 ≤ t < 2048. All center values are also units modulo 9 and 27 on that range, as Corollary 2 predicts. An all-time proof of the observed pattern is not supplied here. If Rule 84 is universal modulo three, it is universal at every power of three; three could not be the sole exceptional modulus.\" Section 19, page 42: \"The classification reduces the remaining single-seed universality question to the eight rules in E at odd primes. The observed Rule 84 pattern modulo three requires an invariant or an all-time recurrence proof. A finite nonzero prefix is insufficient.\" The encoding states A(0, 0) = 1 and the three values at 3s + 1, 3s + 2 and 3s + 3 for every natural s, so every positive time is included. The entries 1 and 2 denote residues in ZMod 3. Universality at higher powers is a consequence using the source's Corollaries 1–2, outside the displayed claim.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The pattern holds for all time", Disp(F.Id("claim")),
                "The half-plane x < 0 remains zero by induction on time, since the polynomial vanishes when its left and center inputs are zero. From time 1 onward, every length-seven window starting at x ≥ −5 lies in one of three finite languages, indexed by time modulo three. They have sizes 35, 37 and 38. Every compatible length-nine word maps to a word in the next language. The distinguished window at x = −5 cycles through 0000011, 0000020 and 0000021 at phases 1, 2 and 0; its left input is zero, and its neighboring window controls the right input. Induction preserves both the language membership and this boundary word. Its sixth letter is the value at x = 0, yielding 1, 2 and 2 in the three phases.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("rule84-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula OrbitFormula()
    {
        Formula t = F.Id("t"), x = F.Id("x");
        Formula a = Call("A", t, Subtract(x, D(1)));
        Formula b = Call("A", t, x);
        Formula c = Call("A", t, Add(x, D(1)));
        Formula start = All("x", Integers(), Equal(Call("A", D(0), x),
            Call("ite", Equal(x, D(0)), D(1), D(0))));
        Formula step = All("t", Naturals(), All("x", Integers(),
            Equal(Call("A", Add(t, D(1)), x),
                Times(Parenthesized(Add(Add(a, b), Times(a, b))),
                    Parenthesized(Add(D(1), c))))));
        return Disp(new Formula.Aligned([
            Seq(F.Id("A"), Colon, Sp, Naturals(), Sp, To, Sp,
                Integers(), Sp, To, Sp, Call("ZMod", D(3))),
            start,
            step]));
    }

    private static Formula ClaimFormula()
    {
        Formula s = F.Id("s");
        Formula time(Formula offset) => Add(Times(D(3), s), offset);
        Formula phases = All("s", Naturals(), And(
            Equal(Call("A", time(D(1)), D(0)), D(1)), And(
                Equal(Call("A", time(D(2)), D(0)), D(2)),
                Equal(Call("A", time(D(3)), D(0)), D(2)))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Parenthesized(And(Equal(Call("A", D(0), D(0)), D(1)), phases))));
    }
}
