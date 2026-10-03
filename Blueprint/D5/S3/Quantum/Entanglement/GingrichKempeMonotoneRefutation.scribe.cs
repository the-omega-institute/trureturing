using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class GingrichKempeMonotoneRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/gingrich2002properties");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gingrich (arXiv:quant-ph/0106042, Phys. Rev. A 65, 052302) proposes sigma_ABC = 3 - (I_1 + I_2 + I_3) I_4, built from three purities and the Kempe invariant I_4, as a fifth entanglement monotone of three-qubit pure states, supported by numerical tests. It is not one: a two-outcome diagonal measurement on qubit A of (5|000> + 5|011> + 2|110>)/(3 sqrt 6) raises its average by 169/1594323.",
        H("Gingrich's proposed three-qubit monotone increases on average under a local measurement"),
        Blocks(
            Node("poly", "Polynomial invariants", PolyFormula(),
                "For a three-qubit vector psi, a function from the configurations Fin 3 -> Fin 2 to the complex numbers with the qubits A, B, C at the indices 0, 1, 2, the amplitude t_{ijk} is psi at (i, j, k). For permutations sigma and tau of n elements, Eq. (8) of the paper sums, over n index triples x_r = (i_r, j_r, k_r), the product over r of t_{i_r j_r k_r} times the complex conjugate of t_{i_r j_{sigma(r)} k_{tau(r)}}.",
                "polyInvariant", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sigma", "The proposed monotone", SigmaFormula(),
                "The paper sets I_1 = P_{e,(12)}, I_2 = P_{(12),e}, I_3 = P_{(12),(12)} on two index triples and the Kempe invariant I_4 = P_{(123),(132)} on three index triples, and proposes sigma_ABC = 3 - (I_1 + I_2 + I_3) I_4. Here e is the identity permutation, swap(0, 1) is the transposition (12) of Fin 2, and finRotate(3), which sends 0 to 1, 1 to 2 and 2 to 0, is the cycle (123), with inverse (132).",
                "sigmaABC", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed monotonicity", ClaimFormula(),
                "The paper calls a function an entanglement monotone if, for every state and every complete local instrument on one party, its value is at least the average of its values on the normalized outcomes, weighted by their probabilities. The displayed statement is this inequality for every normalized three-qubit vector and every complete instrument K_0, ..., K_{n-1} on qubit A (index 0), acting through the existing localOp, the product operator with factor K_k at qubit 0 and the identity elsewhere; the weights p are the outcome probabilities, outcomes with p_k = 0 are omitted, and sigma_ABC enters through its real part.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("psi", "The counterexample state", PsiFormula(),
                "The state is (5|000> + 5|011> + 2|110>)/(3 sqrt 6), with norm one since 25 + 25 + 4 = 54.",
                "psi", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("instrument", "The measurement on qubit A", InstrumentFormula(),
                "The two outcomes are K_0 = diag(3/5, 0) and K_1 = diag(4/5, 1) on qubit A, with K_0^dagger K_0 + K_1^dagger K_1 = I.",
                "instrument", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The proposed monotone increases on average", Disp(new Formula.Not(F.Id("claim"))),
                "For a vector a|000> + b|011> + c|110>, expanding Eq. (8) gives I_1 = (x + z)^2 + y^2, I_2 = x^2 + (y + z)^2, I_3 = (x + y)^2 + z^2 and I_4 = x^3 + y^3 + z^3 + 3xyz with x = |a|^2, y = |b|^2, z = |c|^2. The operator diag(k_0, k_1) on qubit A and a scalar keep this support. The outcome K_0 has probability 1/3 and normalized state (|000> + |011>)/sqrt 2, where sigma_ABC = 5/2; the outcome K_1 has probability 2/3 and normalized state (2|000> + 2|011> + |110>)/3, where sigma_ABC = 16792/6561. The state itself has sigma_ABC = 8097475/3188646, so the average after the measurement, 8097813/3188646, exceeds it by 169/1594323.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gingrich-2002-sigma-abc-monotone"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("gkm-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Of(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Complex() => NumberSet(F.Id("C"));
    private static Formula Fin(byte n) => Call(F.Id("Fin"), D(n));
    private static Formula Vectors() =>
        Seq(Parenthesized(Seq(Fin(3), Sp, To, Sp, Fin(2))), Sp, To, Sp, Complex());
    private static Formula QubitMatrix() => Call(F.Id("Matrix"), Fin(2), Fin(2), Complex());
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula Ket(params byte[] digits) => Seq(Bar, D(digits), Rangle);

    private static Formula Perm(Formula n) => Call(F.Id("Perm"), Call(F.Id("Fin"), n));
    private static Formula ProdOver(Formula index, Formula body) =>
        Seq(Prod, Underscore, Grp(index), Sp, body);
    private static Formula Poly(Formula s, Formula t, Formula psi) =>
        Call(F.Id("polyInvariant"), s, t, psi);
    private static Formula Swap() => Call(F.Id("swap"), D(0), D(1));

    private static Formula PolyFormula()
    {
        Formula n = F.Id("n"), s = SigmaLower, t = Tau, psi = Psi, x = F.Id("x"), r = F.Id("r");
        Formula xr = new Formula.Subscript(x, r);
        Formula triple = Parenthesized(Seq(Of(xr, D(0)), Comma, Sp,
            Of(new Formula.Subscript(x, Of(s, r)), D(1)), Comma, Sp,
            Of(new Formula.Subscript(x, Of(t, r)), D(2))));
        Formula factor = Mul(Of(psi, xr), Call(F.Id("star"), Of(psi, triple)));
        Formula configurations = Seq(Fin(3), Sp, To, Sp, Fin(2));
        Formula index = Seq(x, Sp, Colon, Sp, Call(F.Id("Fin"), n), Sp, To, Sp,
            Parenthesized(configurations));
        Formula value = SumOver(index, ProdOver(r, factor));
        return Disp(All(n, NumberSet(F.Id("N")), All(s, Perm(n), All(t, Perm(n),
            All(psi, Vectors(), EqTo(Poly(s, t, psi), value))))));
    }

    private static Formula SigmaFormula()
    {
        Formula psi = Psi, rot = Call(F.Id("finRotate"), D(3));
        Formula purities = Add(Add(Poly(D(1), Swap(), psi), Poly(Swap(), D(1), psi)),
            Poly(Swap(), Swap(), psi));
        Formula kempe = Poly(rot, Pow(rot, Seq(Minus, D(1))), psi);
        Formula value = Sub(D(3), Mul(Parenthesized(purities), kempe));
        return Disp(All(psi, Vectors(), EqTo(Call(F.Id("sigmaABC"), psi), value)));
    }

    private static Formula ClaimFormula()
    {
        Formula psi = Psi, n = F.Id("n"), k = F.Id("K"), j = F.Id("k"), w = F.Id("w"), p = F.Id("p");
        Formula kj = new Formula.Subscript(k, j);
        Formula pj = new Formula.Subscript(p, j);
        Formula image = Parenthesized(Seq(Call(F.Id("localOp"), D(0), kj), Sp, Cdot, Sp, psi));
        Formula probability = SumOver(w, Pow(Norm(Of(image, w)), D(2)));
        Formula normalized = SumOver(w, Pow(Norm(Of(psi, w)), D(2)));
        Formula complete = EqTo(SumOver(j, Mul(Pow(kj, F.Id("H")), kj)), D(1));
        Formula probabilities = All(j, Call(F.Id("Fin"), n), EqTo(pj, probability));
        Formula outcomes = Seq(j, Sp, Colon, Sp, pj, Sp, Neq, Sp, D(0));
        Formula average = Seq(new Formula.Subscript(Sum, outcomes), Sp,
            Mul(pj, Call(F.Id("re"), Call(F.Id("sigmaABC"), Mul(Frac(D(1), Root(pj)), image)))));
        Formula weights = Seq(Call(F.Id("Fin"), n), Sp, To, Sp, NumberSet(F.Id("R")));
        Formula body = Imp(EqTo(normalized, D(1)),
            All(n, NumberSet(F.Id("N")), All(k, Seq(Call(F.Id("Fin"), n), Sp, To, Sp, QubitMatrix()),
                Imp(complete, All(p, weights,
                    Imp(probabilities, LeTo(average,
                        Call(F.Id("re"), Call(F.Id("sigmaABC"), psi)))))))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, All(psi, Vectors(), body)));
    }

    private static Formula PsiFormula()
    {
        Formula sum = Add(Add(Mul(D(5), Ket(0, 0, 0)), Mul(D(5), Ket(0, 1, 1))), Mul(D(2), Ket(1, 1, 0)));
        return Disp(EqTo(Psi, Mul(Frac(D(1), Mul(D(3), Root(D(6)))), Parenthesized(sum))));
    }

    private static Formula InstrumentFormula()
    {
        Formula k = F.Id("K");
        Formula first = EqTo(new Formula.Subscript(k, D(0)),
            Call(F.Id("diag"), Frac(D(3), D(5)), D(0)));
        Formula second = EqTo(new Formula.Subscript(k, D(1)),
            Call(F.Id("diag"), Frac(D(4), D(5)), D(1)));
        return Disp(Seq(first, Comma, Qquad, Sp, second));
    }
}
