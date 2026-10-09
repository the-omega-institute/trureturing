using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.TridiagonalSweeps;

internal sealed class TokenDampedSweepContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/wallner2026passbucket");
    private const string Conjecture =
        "Conjecture 1 (Spectral contraction): The damped transfer map Mα is repeatedly "
        + "applied and its spectral radius satisfies ρ(Mα) < 1, such that u → 0 for 0 < α < 1.";
    private const string Stacking =
        "Stacking these m relations yields a three-banded system A x′ = B x + c ⇔ "
        + "x′ = A⁻¹ B x + A⁻¹ c, where A and B reflect the coefficients of x′ and x "
        + "in the odd/even relations, and c collects the constants.";
    private const string Token =
        "This changes only the first pair’s relation: 2x₁/v₁ + (x′₁ − x₁)/(αv₁) = "
        + "(x₂ − x₁)/v₂ + (x₂ − x′₁)/v₂, all other equations remain unchanged. "
        + "In matrix form, with the same A, replace B by Bα and obtain u′ = Mαu, "
        + "with Mα := A⁻¹Bα.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Token-1 damping strictly contracts the spectrum and every centered trajectory.",
        H("Spectral contraction of the Token-1 transfer map"),
        Blocks(
            Node("stacked-left", "The stacked next-coordinate matrix", "A",
                MatrixFormula("A", LeftEntries()), Stacking + " (Section IV, page 3.) "
                + "The source has m = n − 1 adjacent pairs. Pair i here has source index "
                + "i + 1; an odd source row therefore has i.val mod 2 = 0. "
                + "The velocities of its two robots are v(Fin.castSucc i) and v(Fin.succ i). "
                + "The centered endpoint coordinates are zero.",
                DescribeRole.Definition),
            Node("stacked-right", "The stacked original-coordinate matrix", "B",
                MatrixFormula("B", RightEntries()), Stacking + " (Section IV, page 3.) "
                + "These are exactly the coefficients of the original coordinates "
                + "in the source odd/even relations; missing neighbors contribute zero.",
                DescribeRole.Definition),
            Node("token-row", "The Token-1 right-coordinate matrix", "Balpha",
                DampedMatrixFormula(), Token + " (Section IV.B.1, page 4.) "
                + "The displayed real parameter a denotes the source α. Solving the "
                + "first travel-time equation for x′₁ gives the displayed first row. "
                + "Every remaining row equals B. B_α displays the Lean definition Balpha.",
                DescribeRole.Definition),
            Node("transfer-map", "The literal damped transfer map", "Malpha",
                TransferFormula(), Token + " (Section IV.B.1, page 4.) "
                + "The displayed a denotes α. Matrix inverse is Mathlib's inverse; "
                + "positive velocities make A invertible. M_α displays the Lean definition Malpha.",
                DescribeRole.Definition),
            Node("conjecture", "Conjecture 1 in all finite dimensions", "claim",
                Eq(Call("claim"), Parenthesized(ClaimFormula())),
                Conjecture + " (Section IV.B.1, page 4.) "
                + "The encoding ranges over every m ≥ 1, every positive vector "
                + "v : Fin(m + 1) → ℝ and every real a with 0 < a < 1. "
                + "The first conjunct bounds every complex spectral value of "
                + "the complexification of Mα. In finite dimension this is "
                + "strict spectral-radius contraction. The second conjunct states "
                + "Filter.Tendsto to the zero real vector for every initial u. "
                + "The same damped map is used at every power.",
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("token-spectral-contraction"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Strict spectrum bound and convergence"),
                StatementSource.FromAuthor(Disp(Call("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The weighted Dirichlet form Q(z) is the sum of "
                    + "|zⱼ − zⱼ₋₁|²/vⱼ with both endpoint values zero. "
                    + "Every local reflection preserves Q. The damped event "
                    + "is (1 − θ)I + θE₁, where "
                    + "θ = a(v₁ + v₂)/(v₂ + av₁) lies strictly between zero and one. "
                    + "Its Q-loss vanishes exactly when E₁ fixes the vector. "
                    + "A hypothetical unit-modulus eigenvector is then an "
                    + "undamped eigenvector fixed by E₁. For eigenvalue one, "
                    + "weighted Dirichlet rigidity forces zero; for every other "
                    + "unit-modulus eigenvalue, its first coordinate vanishes "
                    + "and the row recurrence propagates zero through the chain. "
                    + "Thus every spectral modulus is strictly below one. "
                    + "The finite-dimensional power-decay theorem gives "
                    + "convergence of every real centered trajectory."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance"))
        ]));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula LeftEntries()
    {
        var i = F.Id("i");
        var j = F.Id("j");
        return If(Even(i), If(Eq(i, j), D(1), D(0)),
            If(Eq(i, j), VelocitySum(i),
                If(Eq(Add(Call("val", j), D(1)), Call("val", i)),
                    new Formula.Negate(Mul(D(2), Velocity(i, "succ"))),
                    If(Eq(Add(Call("val", i), D(1)), Call("val", j)),
                        new Formula.Negate(Mul(D(2), Velocity(i, "castSucc"))), D(0)))));
    }

    private static Formula RightEntries()
    {
        var i = F.Id("i");
        var j = F.Id("j");
        return If(Even(i),
            If(Eq(i, j), new Formula.Negate(D(1)),
                If(Eq(Add(Call("val", j), D(1)), Call("val", i)),
                    new Formula.Fraction(Mul(D(2), Velocity(i, "succ")), VelocitySum(i)),
                    If(Eq(Add(Call("val", i), D(1)), Call("val", j)),
                        new Formula.Fraction(Mul(D(2), Velocity(i, "castSucc")), VelocitySum(i)),
                        D(0)))),
            If(Eq(i, j), new Formula.Negate(VelocitySum(i)), D(0)));
    }

    private static Formula MatrixFormula(string name, Formula entries) =>
        All("m", Naturals(), All("v", Vector(Add(F.Id("m"), D(1)), Reals()),
            All("i", Fin(F.Id("m")), All("j", Fin(F.Id("m")),
                Eq(Call(name, F.Id("m"), F.Id("v"), F.Id("i"), F.Id("j")), entries)))));

    private static Formula DampedMatrixFormula()
    {
        var i = F.Id("i");
        var j = F.Id("j");
        var a = F.Id("a");
        var den = Add(Velocity(i, "succ"), Mul(a, Velocity(i, "castSucc")));
        var entries = If(Eq(Call("val", i), D(0)),
            If(Eq(i, j),
                new Formula.Fraction(
                    Sub(Mul(Velocity(i, "succ"), Sub(D(1), Mul(D(2), a))),
                        Mul(a, Velocity(i, "castSucc"))), den),
                If(Eq(Add(Call("val", i), D(1)), Call("val", j)),
                    new Formula.Fraction(Mul(Mul(D(2), a), Velocity(i, "castSucc")), den),
                    D(0))),
            Call("B", F.Id("m"), F.Id("v"), i, j));
        return All("m", Naturals(), All("v", Vector(Add(F.Id("m"), D(1)), Reals()),
            All("a", Reals(), All("i", Fin(F.Id("m")), All("j", Fin(F.Id("m")),
                Eq(Apply(BAlpha(), F.Id("m"), F.Id("v"), a, i, j), entries))))));
    }

    private static Formula TransferFormula() =>
        All("m", Naturals(), All("v", Vector(Add(F.Id("m"), D(1)), Reals()),
            All("a", Reals(), Eq(Apply(MAlpha(), F.Id("m"), F.Id("v"), F.Id("a")),
                Mul(new Formula.Power(Call("A", F.Id("m"), F.Id("v")),
                    new Formula.Negate(D(1))),
                    Apply(BAlpha(), F.Id("m"), F.Id("v"), F.Id("a")))))));

    private static Formula ClaimFormula()
    {
        var m = F.Id("m");
        var v = F.Id("v");
        var a = F.Id("a");
        var map = Apply(MAlpha(), m, v, a);
        var complexified = QualifiedCall("Matrix", "map", map,
            Call("algebraMap", Reals(), Complexes()));
        var spec = All("c", Complexes(),
            Implies(new Formula.Relation(F.Id("c"), FormulaRelationOperator.MemberOf,
                    Call("spectrum", Complexes(), complexified)),
                Lt(new Formula.Norm(F.Id("c")), D(1))));
        var decay = All("u", Vector(m, Reals()),
            QualifiedCall("Filter", "Tendsto",
                Parenthesized(Seq(LambdaLower, Sp, F.Id("k"), Colon, Naturals(), Comma,
                    QualifiedCall("Matrix", "mulVec", new Formula.Power(map, F.Id("k")),
                        F.Id("u")))),
                Qualified("Filter", "atTop"), Call("nhds", D(0))));
        return All("m", Naturals(), Implies(Le(D(1), m),
            All("v", Vector(Add(m, D(1)), Reals()),
                Implies(All("j", Fin(Add(m, D(1))), Lt(D(0), Apply(v, F.Id("j")))),
                    All("a", Reals(), Implies(Lt(D(0), a),
                        Implies(Lt(a, D(1)), And(spec, decay))))))));
    }

    private static Formula BAlpha() => new Formula.Subscript(F.Id("B"), Alpha);
    private static Formula MAlpha() => new Formula.Subscript(F.Id("M"), Alpha);
    private static Formula Even(Formula i) =>
        Eq(new Formula.Modulo(Call("val", i), D(2)), D(0));
    private static Formula Velocity(Formula i, string index) =>
        Apply(F.Id("v"), QualifiedCall("Fin", index, i));
    private static Formula VelocitySum(Formula i) =>
        Add(Velocity(i, "castSucc"), Velocity(i, "succ"));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Vector(Formula n, Formula field) =>
        new Formula.TypeArrow(Fin(n), field);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula QualifiedCall(string owner, string name, params Formula[] args) =>
        Apply(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula If(Formula p, Formula yes, Formula no) => Call("ite", p, yes, no);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
}
