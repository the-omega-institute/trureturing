using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class FibonacciModFourClockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/FibonacciModFourClock.";
    private static readonly Formula Cx = Seq(Mathbb, Grp(F.Id("C")));
    private static readonly Formula Rx = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula Four = Call("Fin", D(4));
    private static readonly Formula Joint = Seq(Four, Times, Four);
    private static readonly Formula Mat = Call("Matrix", Joint, Joint, Cx);
    private static readonly Formula Unit = Call("identity", Joint);
    private static readonly Formula U = F.Id("U"), L = F.Id("L"), Z = F.Id("z");
    private static readonly Formula T = F.Id("Delta"), X = F.Id("x"), R = F.Id("r");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The standard mod-four digit lift has four energies and an exact exponential polynomial "
            + "on the entire sixteen-dimensional joint space.",
        H("The Actual Mod-Four Fibonacci Clock"),
        Blocks(
            Node("digits", "The standard digit permutation", DigitFormula(),
                "Each four-label factor represents a bit pair by 2b0+b1. The joint pair "
                    + "represents the standard coordinate split a+2h. The high update includes "
                    + "the carry from the sum of the two low bits.", "digitMap", DescribeRole.Definition),
            Node("permutation", "The invertible digit action", PermutationFormula(),
                "Five applications of the digit map give its inverse. Its sixth application "
                    + "fixes every joint label.", "digitPermutation", DescribeRole.Definition),
            Node("lift", "The actual lift matrix", LiftFormula(),
                "The column indexed by a joint label is the basis vector indexed by its "
                    + "digit-map image.", "U", DescribeRole.Definition),
            Node("hamiltonian", "The source Hamiltonian", HamiltonianFormula(),
                "The Hamiltonian is twice the identity minus the lift and its adjoint.",
                "L", DescribeRole.Definition),
            Node("clock", "The actual exponential gate", ClockFormula(),
                "The gate uses the Hamiltonian exponential at the declared time.",
                "clock", DescribeRole.Definition),
            Node("energies", "The four energy labels", EnergyFormula(),
                "The energy labels are ordered as zero, one, three and four.",
                "energy", DescribeRole.Definition),
            Node("pieces", "Polynomial spectral pieces", PiecesFormula(),
                "These four polynomials sum to identity. The Hamiltonian acts on each "
                    + "piece by its corresponding energy.", "spectralPiece", DescribeRole.Definition),
            Node("formula", "The exact clock polynomial", TheoremFormula(),
                "The sixth-power identity and the four eigenpiece equations yield the "
                    + "exponential by applying its eigenvector action to every column. "
                    + "The result uses the full joint space and every real time.",
                "fixed_clock_formula", DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula For(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula EqOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Scale(Formula a, Formula b) => Call("smul", a, b);
    private static Formula Pow(Formula a, byte n) => new Formula.Power(a, D(n));
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Typed(string name, Formula type, Formula value, Formula body) =>
        Call("let", Seq(F.Id(name), Colon, type), value, body);

    private static Formula DigitFormula()
    {
        Formula av = Call("value", Call("fst", Z)), hv = Call("value", Call("snd", Z));
        Formula a0 = Call("floor", Fraction(av, D(2))), a1 = Call("mod", av, D(2));
        Formula h0 = Call("floor", Fraction(hv, D(2))), h1 = Call("mod", hv, D(2));
        Formula carry = Call("floor", Fraction(Add(a0, a1), D(2)));
        Formula low = Call("fin", Add(Mul(D(2), a1), Call("mod", Add(a0, a1), D(2))));
        Formula high = Call("fin", Add(Mul(D(2), h1), Call("mod", Add(Add(h0, h1), carry), D(2))));
        return Disp(For("z", Joint, EqOf(Call("digitMap", Z), Call("pair", low, high))));
    }

    private static Formula PermutationFormula() => Disp(Seq(
        F.Id("digitPermutation"), Colon, Call("Perm", Joint), Eq,
        Call("equivalence", F.Id("digitMap"), Call("iterate", F.Id("digitMap"), D(5)))));

    private static Formula LiftFormula() => Disp(For("i", Joint, For("j", Joint,
        EqOf(Call("entry", U, F.Id("i"), F.Id("j")), Call("if",
            EqOf(F.Id("i"), Call("digitMap", F.Id("j"))), D(1), D(0))))));

    private static Formula HamiltonianFormula() => Disp(EqOf(L,
        Sub(Sub(Scale(D(2), Unit), U), Call("star", U))));

    private static Formula ClockFormula() => Disp(For("Delta", Rx, EqOf(Call("clock", T),
        Call("exp", Scale(Mul(Neg(F.Id("i")), Call("ofReal", T)), L)))));

    private static Formula EnergyFormula() => Disp(For("r", Four, EqOf(Call("energy", R),
        Call("at", Call("vector", D(0), D(1), D(3), D(4)), R))));

    private static Formula PieceVector()
    {
        Formula u2 = Pow(U, 2), u3 = Pow(U, 3), u4 = Pow(U, 4), u5 = Pow(U, 5);
        Formula q0 = Add(Add(Add(Add(Add(Unit, U), u2), u3), u4), u5);
        Formula q1 = Add(Sub(Sub(Sub(Add(Scale(D(2), Unit), U), u2), Scale(D(2), u3)), u4), u5);
        Formula q3 = Sub(Sub(Add(Sub(Sub(Scale(D(2), Unit), U), u2), Scale(D(2), u3)), u4), u5);
        Formula q4 = Sub(Add(Sub(Add(Sub(Unit, U), u2), u3), u4), u5);
        return Call("vector", q0, q1, q3, q4);
    }

    private static Formula PiecesFormula() => Disp(For("r", Four,
        EqOf(Call("spectralPiece", R), Scale(Fraction(D(1), D(6)), Call("at", PieceVector(), R)))));

    private static Formula TheoremFormula()
    {
        Formula pp = F.Id("Pplus"), pm = F.Id("Pminus");
        Formula a = F.Id("A"), b = F.Id("B"), c = F.Id("C");
        Formula polynomial = Add(Add(Add(Scale(a, pp), Scale(b, pm)),
            Scale(c, Mul(U, Add(pp, Scale(X, pm))))), Scale(c, Mul(Pow(U, 2), Sub(pp, Scale(X, pm)))));
        Formula body = new Formula.Logic(EqOf(Pow(U, 6), Unit), FormulaLogicOperator.And,
            EqOf(Call("clock", T), polynomial));
        body = Typed("C", Cx, Fraction(Sub(D(1), Pow(X, 3)), D(3)), body);
        body = Typed("B", Cx, Fraction(Mul(X, Add(D(2), Pow(X, 3))), D(3)), body);
        body = Typed("A", Cx, Fraction(Add(D(1), Mul(D(2), Pow(X, 3))), D(3)), body);
        body = Typed("Pminus", Mat, Scale(Fraction(D(1), D(2)), Sub(Unit, Pow(U, 3))), body);
        body = Typed("Pplus", Mat, Scale(Fraction(D(1), D(2)), Add(Unit, Pow(U, 3))), body);
        body = Typed("x", Cx, Call("exp", Mul(Neg(F.Id("i")), Call("ofReal", T))), body);
        return Disp(For("Delta", Rx, body));
    }

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, DescribeRole role) => Describe.Lean(
        DescribeId.Create("fibonacci-mod-four-clock-" + id), DeclarationHandle.Create(Prefix + declaration),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);
}
