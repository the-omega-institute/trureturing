using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class CalibratedJointMeasurabilityOptimalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/beyer2022jointmeasurability");
    private const string Conjecture = "Page 4: “The ansatz for the effects W^U_ab in Eq. (6) is a priori not the most general one [54]. However, numerical simulations suggest that our visibility bounds are tight and we conjecture that our construction is optimal to satisfy condition (ii) for the given model Eq. (5)”.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fluctuation condition forces the optimal calibrated visibility bound.",
        H("Optimal visibility for calibrated joint measurements"),
        Blocks(
            Node("effA", "Initial white-noise effects",
                Disp(All("d", Field("N"), All("lam", Field("R"), All("a", Fin(V("d")),
                    Equal(Call("effA", V("d"), V("lam"), V("a")), Effect(V("d"), V("lam"), V("a"))))))),
                "Equation (5), p. 3: A_a = λΠ_a + ((1−λ)/d)𝟙. The initial energy projectors are standard matrix units.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("effB", "Final white-noise effects",
                Disp(All("d", Field("N"), All("gam", Field("R"), All("b", Fin(V("d")),
                    Equal(Call("effB", V("d"), V("gam"), V("b")), Effect(V("d"), V("gam"), V("b"))))))),
                "Equation (5), p. 3: B_b = γΠ′_b + ((1−γ)/d)𝟙. The final energy projectors are standard matrix units before the unitary rotation.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("effBU", "Rotated final effects", RotatedFormula(),
                "Page 3: B^U_b = U†B_bU. Both energy bases are represented by standard matrix units; varying U over Matrix.unitaryGroup covers arbitrary relative bases. The final white-noise effect is effB from Eq. (5).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("luders", "The Lüders instrument", LudersFormula(),
                "Page 3 uses the Lüders instrument I^A_a(ρ) = A_a^{1/2}ρA_a^{1/2}. The positive square root is CFC.sqrt on complex matrices.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("AverageCondition", "The average condition", AverageFormula(),
                "Page 3: “(i) Average condition: The average operator of W^U agrees with the difference of the average operators of B^U and A for all choices of f and g”. The real energy assignments f and g are arbitrary, and their difference multiplies each joint effect.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("FluctuationCondition", "The fluctuation condition", FluctuationFormula(),
                "Page 3: “(ii) Fluctuation condition: For states ρ_Δ diagonal in the initial energy eigenbasis the statistics given by W^U agrees with the sequentially measured GTPM statistics”. The states are all positive semidefinite complex matrices of trace one whose off-diagonal entries vanish. Equality holds for each pair of outcomes.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("kappa", "The coherence coefficient", KappaFormula(),
                "Equation (9), p. 4 defines κ = 2√(λ + (1−λ)/d)√((1−λ)/d) + (d−2)(1−λ)/d. The two distinguished levels contribute the square-root products; the other d−2 levels contribute the common diagonal coefficient.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("visibilityBound", "The visibility bound", BoundFormula(),
                "Equation (8), p. 4 gives γ ≤ 2κ/(d + 2κ − dκ). The divisions are real divisions; d is coerced from a natural number to a real number.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Optimality of the calibrated visibility", ClaimFormula(),
                Conjecture + " The encoding states necessity of Eq. (8) for every d ≥ 2 and 0 < lam, gam < 1 when every intermediate unitary has a parent POVM satisfying (i) and (ii). IsPOVM is the positive-effect and normalization predicate from ConcealmentKernelNecessityRefutation. The source proves sufficiency by its inverse Lüders construction.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "No parent POVM exceeds the bound", Disp(V("claim")),
                "Evaluating the fluctuation condition on each diagonal matrix unit fixes every parent effect's diagonal to the product of the two marginal diagonals. CartesianVariance.psd_entry_bound and the triangle inequality bound the sum of coherences between two levels. A Hadamard rotation of those levels gives gam/2 ≤ kappa d lam · (gam/2 + (1−gam)/d). The identity kappa d lam = 1 − (√(lam+(1−lam)/d) − √((1−lam)/d))² ensures a positive denominator, yielding the visibility bound. This proves necessity for arbitrary parent effects. Sufficiency is the source's theorem and is not asserted by the Lean result.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("beyer-uola-luoma-strunz-2022-calibrated-visibility-optimality"),
                    ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("calibrated-visibility-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(Parenthesized(x), op, Parenthesized(y));
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula IffFormula(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Parenthesized(x), FormulaBinaryOperator.Multiply, Parenthesized(y));
    private static Formula Smul(Formula x, Formula y) => At(Q("HSMul", "hSMul"), x, y);
    private static Formula Field(string k) => Seq(Mathbb, Grp(V(k)));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Mat(Formula d) => Call("Matrix", Fin(d), Fin(d), Field("C"));
    private static Formula Fun(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula ProdType(Formula x, Formula y) => Seq(x, Sp, Times, Sp, y);
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Sp, Colon, Sp, type));
    private static Formula ComplexCast(Formula x) => Cast(x, Field("C"));
    private static Formula RealCast(Formula x) => Cast(x, Field("R"));
    private static Formula Fraction(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula Trace(Formula x) => At(Q("Matrix", "trace"), x);
    private static Formula PSD(Formula x) => At(Q("Matrix", "PosSemidef"), x);
    private static Formula Sqrt(Formula x) => At(Q("Real", "sqrt"), x);
    private static Formula SumFin(string name, Formula d, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(V(name), Colon, Fin(d))), Sp, Parenthesized(body));
    private static Formula Effect(Formula d, Formula l, Formula a) => Add(
        Smul(ComplexCast(l), At(Q("Matrix", "single"), a, a, D(1))),
        Smul(ComplexCast(Fraction(Sub(D(1), l), RealCast(d))), D(1)));
    private static Formula RotatedCall(Formula gam, Formula u) => Seq(Operatorname, Grp(V("effBU")), Parenthesized(Seq(V("gam"), Sp, Colon, Eq, Sp, gam)), Parenthesized(u));
    private static Formula RotatedFormula() => Disp(All("d", Field("N"), All("gam", Field("R"), All("U", Mat(V("d")), All("b", Fin(V("d")),
        Equal(At(RotatedCall(V("gam"), V("U")), V("b")), Mul(Mul(Call("star", V("U")), Call("effB", V("d"), V("gam"), V("b"))), V("U"))))))));
    private static Formula LudersFormula() => Disp(All("d", Field("N"), All("A", Mat(V("d")), All("rho", Mat(V("d")),
        Equal(Call("luders", V("A"), V("rho")), Mul(Mul(At(Q("CFC", "sqrt"), V("A")), V("rho")), At(Q("CFC", "sqrt"), V("A"))))))));
    private static Formula Parameters(Formula body) => All("d", Field("N"), All("W", Fun(ProdType(Fin(V("d")), Fin(V("d"))), Mat(V("d"))),
        All("A", Fun(Fin(V("d")), Mat(V("d"))), All("B", Fun(Fin(V("d")), Mat(V("d"))), body))));
    private static Formula AverageFormula()
    {
        Formula d = V("d"), a = V("a"), b = V("b"), f = V("f"), g = V("g");
        Formula lhs = SumFin("a", d, SumFin("b", d, Smul(ComplexCast(Sub(At(g, b), At(f, a))), At(V("W"), Pair(a, b)))));
        Formula rhs = Sub(SumFin("b", d, Smul(ComplexCast(At(g, b)), At(V("B"), b))), SumFin("a", d, Smul(ComplexCast(At(f, a)), At(V("A"), a))));
        return Disp(Parameters(IffFormula(Call("AverageCondition", V("W"), V("A"), V("B")),
            All("f", Fun(Fin(d), Field("R")), All("g", Fun(Fin(d), Field("R")), Equal(lhs, rhs))))));
    }
    private static Formula FluctuationFormula()
    {
        Formula d = V("d"), rho = V("rho"), i = V("i"), j = V("j"), a = V("a"), b = V("b");
        Formula diagonal = All("i", Fin(d), All("j", Fin(d), Implies(Rel(i, FormulaRelationOperator.NotEqual, j), Equal(At(rho, i, j), D(0)))));
        Formula stats = All("a", Fin(d), All("b", Fin(d), Equal(Trace(Mul(At(V("W"), Pair(a, b)), rho)), Trace(Mul(At(V("B"), b), Call("luders", At(V("A"), a), rho))))));
        return Disp(Parameters(IffFormula(Call("FluctuationCondition", V("W"), V("A"), V("B")),
            All("rho", Mat(d), Implies(PSD(rho), Implies(Equal(Trace(rho), D(1)), Implies(diagonal, stats)))))));
    }
    private static Formula KappaFormula()
    {
        Formula d = V("d"), lam = V("lam"), s = Fraction(Sub(D(1), lam), RealCast(d));
        return Disp(All("d", Field("N"), All("lam", Field("R"), Equal(Call("kappa", d, lam),
            Add(Mul(Mul(D(2), Sqrt(Add(lam, s))), Sqrt(s)), Mul(Sub(RealCast(d), D(2)), s))))));
    }
    private static Formula BoundFormula()
    {
        Formula d = V("d"), lam = V("lam"), k = Call("kappa", d, lam);
        return Disp(All("d", Field("N"), All("lam", Field("R"), Equal(Call("visibilityBound", d, lam),
            Fraction(Mul(D(2), k), Sub(Add(RealCast(d), Mul(D(2), k)), Mul(RealCast(d), k)))))));
    }
    private static Formula ClaimFormula()
    {
        Formula d = V("d"), lam = V("lam"), gam = V("gam"), u = V("U"), w = V("W");
        Formula effects = Call("effA", d, lam);
        Formula rotated = RotatedCall(gam, u);
        Formula parent = Some("W", Fun(ProdType(Fin(d), Fin(d)), Mat(d)), And(At(Q("ConcealmentKernelNecessityRefutation", "IsPOVM"), w),
            And(Call("AverageCondition", w, effects, rotated), Call("FluctuationCondition", w, effects, rotated))));
        Formula allU = All("U", Mat(d), Implies(Rel(u, FormulaRelationOperator.MemberOf, At(Q("Matrix", "unitaryGroup"), Fin(d), Field("C"))), parent));
        Formula bounds = Implies(Rel(D(0), FormulaRelationOperator.LessThan, lam), Implies(Rel(lam, FormulaRelationOperator.LessThan, D(1)),
            Implies(Rel(D(0), FormulaRelationOperator.LessThan, gam), Implies(Rel(gam, FormulaRelationOperator.LessThan, D(1)),
                Implies(allU, Rel(gam, FormulaRelationOperator.LessThanOrEqual, Call("visibilityBound", d, lam)))))));
        return Disp(IffFormula(V("claim"), All("d", Field("N"), Implies(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, d),
            All("lam", Field("R"), All("gam", Field("R"), bounds))))));
    }
}
