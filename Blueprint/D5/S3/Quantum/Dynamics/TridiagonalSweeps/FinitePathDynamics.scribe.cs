using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.TridiagonalSweeps;

internal sealed class FinitePathDynamicsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted finite-path rigidity, boundary observability, and spectral power decay.",
        H("Finite-path rigidity and matrix decay"),
        Blocks(
            Node("zero-extension", "Zero endpoint extension", "zeroExtend",
                All("m", Naturals(), All("z", Vector(F.Id("m"), Complexes()),
                    Eq(Call("zeroExtend", F.Id("z")),
                        QualifiedCall("Fin", "cases", D(0),
                            QualifiedCall("Fin", "snoc", F.Id("z"), D(0)))))),
                "For every m and complex vector z on Fin m, Fin.cases places zero at "
                + "the left endpoint and Fin.snoc places zero at the right endpoint. "
                + "The resulting vector has domain Fin(m + 2).",
                DescribeRole.Definition),
            Node("interior-extension", "The interior values are unchanged", "extend_interior",
                All("m", Naturals(), All("z", Vector(F.Id("m"), Complexes()),
                    All("i", Fin(F.Id("m")), Eq(
                        Apply(Call("zeroExtend", F.Id("z")),
                            QualifiedCall("Fin", "succ",
                                QualifiedCall("Fin", "castSucc", F.Id("i")))),
                        Apply(F.Id("z"), F.Id("i")))))),
                "Interior coordinate i is coordinate i + 1 of the zero endpoint extension.",
                DescribeRole.Lemma),
            Node("last-extension", "The right endpoint is zero", "extend_last",
                All("m", Naturals(), All("z", Vector(F.Id("m"), Complexes()),
                    Eq(Apply(Call("zeroExtend", F.Id("z")),
                        QualifiedCall("Fin", "last", Add(F.Id("m"), D(1)))), D(0)))),
                "The last coordinate of the extended vector is zero.",
                DescribeRole.Lemma),
            Node("harmonic-rigidity", "Weighted harmonic Dirichlet rigidity",
                "harmonic_dirichlet_zero", HarmonicFormula(),
                "For arbitrary m and positive velocities, equal adjacent weighted slopes "
                + "force every interior complex coordinate to vanish. Finite induction "
                + "makes all edge slopes equal. Their telescoping sum is zero; "
                + "the strictly positive total velocity forces the common slope to zero.",
                DescribeRole.Theorem),
            Node("boundary-observability", "A boundary zero propagates through the path",
                "boundary_zero_observability", ObservabilityFormula(),
                "For m ≥ 1, a zero first interior coordinate and a recurrence propagating "
                + "two adjacent zeros imply that the entire vector is zero. "
                + "The left endpoint supplied by zeroExtend starts the induction.",
                DescribeRole.Theorem),
            Node("matrix-power-decay", "Strict spectral bounds give real trajectory decay",
                "real_mulVec_powers_tendsto_zero", DecayFormula(),
                "For m ≥ 1 and a real matrix N, every complex spectral modulus below one "
                + "implies convergence of (N^k).mulVec u to zero for every real vector u. "
                + "Gelfand's formula gives an eventual geometric bound on matrix powers "
                + "in the complex operator norm. Continuity of matrix-vector multiplication "
                + "and of coordinatewise real parts yields the real trajectory limit.",
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula HarmonicFormula()
    {
        var i = F.Id("i");
        var left = QualifiedCall("Fin", "castSucc", QualifiedCall("Fin", "castSucc", i));
        var right = QualifiedCall("Fin", "succ", QualifiedCall("Fin", "succ", i));
        var fixedSlopes = All("i", Fin(F.Id("m")),
            Eq(new Formula.Fraction(Sub(Apply(F.Id("z"), i), Extended(left)),
                    CastComplex(Apply(F.Id("v"), QualifiedCall("Fin", "castSucc", i)))),
                new Formula.Fraction(Sub(Extended(right), Apply(F.Id("z"), i)),
                    CastComplex(Apply(F.Id("v"), QualifiedCall("Fin", "succ", i))))));
        return All("m", Naturals(), All("v", Vector(Add(F.Id("m"), D(1)), Reals()),
            Implies(PositiveVelocities(), All("z", Vector(F.Id("m"), Complexes()),
                Implies(fixedSlopes, Eq(F.Id("z"), D(0)))))));
    }

    private static Formula ObservabilityFormula()
    {
        var i = F.Id("i");
        var propagate = All("i", Fin(F.Id("m")),
            Implies(Eq(Apply(F.Id("z"), i), D(0)),
                Implies(Eq(Extended(QualifiedCall("Fin", "castSucc",
                        QualifiedCall("Fin", "castSucc", i))), D(0)),
                    Eq(Extended(QualifiedCall("Fin", "succ",
                        QualifiedCall("Fin", "succ", i))), D(0)))));
        // Fin.mk's proof argument is proof-irrelevant and omitted from the display.
        var first = QualifiedCall("Fin", "mk", D(0));
        return All("m", Naturals(), Implies(Le(D(1), F.Id("m")),
            All("z", Vector(F.Id("m"), Complexes()),
                Implies(Eq(Apply(F.Id("z"), first), D(0)),
                    Implies(propagate, Eq(F.Id("z"), D(0)))))));
    }

    private static Formula DecayFormula()
    {
        var m = F.Id("m");
        var n = F.Id("N");
        var complexified = QualifiedCall("Matrix", "map", n,
            Call("algebraMap", Reals(), Complexes()));
        var spec = All("c", Complexes(),
            Implies(new Formula.Relation(F.Id("c"), FormulaRelationOperator.MemberOf,
                    Call("spectrum", Complexes(), complexified)),
                Lt(new Formula.Norm(F.Id("c")), D(1))));
        var decay = QualifiedCall("Filter", "Tendsto",
            Parenthesized(Seq(LambdaLower, Sp, F.Id("k"), Colon, Naturals(), Comma,
                QualifiedCall("Matrix", "mulVec", new Formula.Power(n, F.Id("k")), F.Id("u")))),
            Qualified("Filter", "atTop"), Call("nhds", D(0)));
        return All("m", Naturals(), Implies(Le(D(1), m),
            All("N", Call("Matrix", Fin(m), Fin(m), Reals()),
                Implies(spec, All("u", Vector(m, Reals()), decay)))));
    }

    private static Formula PositiveVelocities() =>
        All("j", Fin(Add(F.Id("m"), D(1))), Lt(D(0), Apply(F.Id("v"), F.Id("j"))));
    private static Formula Extended(Formula index) =>
        Apply(Call("zeroExtend", F.Id("z")), index);
    private static Formula CastComplex(Formula value) =>
        Parenthesized(Seq(value, Colon, Complexes()));
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
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
