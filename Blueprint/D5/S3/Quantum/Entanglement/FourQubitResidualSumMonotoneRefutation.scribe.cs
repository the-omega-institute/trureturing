using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FourQubitResidualSumMonotoneRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/bai2007multipartite");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bai, Yang and Wang (arXiv:quant-ph/0703098, Phys. Rev. A 76, 022336) conjecture that the sum of the residual correlations M = sum_k tau_k - 2 sum_{p<q} C_pq^2 of a four-qubit pure state, built from the one-qubit linear entropies and Wootters' concurrences of the pairs, is an entanglement monotone. It is not: a two-outcome diagonal measurement on one qubit of the state (20|0001> + 2|1000> + 6|1011> + |1110>)/21 raises the average of M from 7552/194481 to 3528832/85766121.",
        H("The residual-correlation sum of four qubits is not an entanglement monotone"),
        Blocks(
            Node("tau", "Linear entropy", TauFormula(),
                "For a four-qubit vector psi, a function from the configurations Fin 4 -> Fin 2 to the complex numbers with the qubits A, B, C, D at the indices 0, 1, 2, 3, the reduced state of the qubit k is the existing reducedState, the partial trace of the projector onto psi over the other three qubits. The linear entropy of the qubit k is tau_k = 2 (1 - Tr rho_k^2).",
                "linearEntropy", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conc", "Concurrence of a pair", ConcFormula(),
                "For two qubits p and q, rho is the reduced state of the pair {p, q} (the existing reducedState) and the existing timeReversed applies sigma_y to each qubit of the pair after complex conjugation, so that rho timeReversed(rho) is the matrix rho_pq (sigma_y x sigma_y) rho_pq^* (sigma_y x sigma_y) of Wootters' formula. The list l consists of the real parts of the roots of its characteristic polynomial, with multiplicity, sorted decreasingly; getD(l, i, 0) is its entry at position i, or 0 when the list is shorter. The concurrence is max(sqrt(l_0) - sqrt(l_1) - sqrt(l_2) - sqrt(l_3), 0); for p different from q the four entries are the eigenvalues lambda_1 >= lambda_2 >= lambda_3 >= lambda_4 of the paper.",
                "concurrence", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("m", "The sum of the residual correlations", ResidualFormula(),
                "Eq. (7) of the paper: M = sum_k tau_k - 2 sum_{p>q} C_pq^2 over the four qubits and the six pairs; each pair is counted once, here as p < q.",
                "residualSum", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured monotonicity", ClaimFormula(),
                "An entanglement monotone does not increase on average under LOCC. A complete instrument K_0, ..., K_{n-1} on qubit A, with sum_j K_j^dagger K_j = I, is a one-step LOCC protocol; K_j acts on qubit A (index 0) through the existing localOp, the product operator with factor K_j at qubit 0 and the identity elsewhere, applied to psi by matrix-vector multiplication: the outcome j occurs with probability p_j = ||K_j psi||^2 (the weights p of the display) and leaves the normalized state K_j psi / sqrt(p_j). The displayed statement asserts sum_j p_j M(K_j psi / sqrt(p_j)) <= M(psi) for every normalized four-qubit vector and every such instrument, omitting the outcomes with p_j = 0; it is a consequence of the conjecture that M is an entanglement monotone.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pair-equiv", "Coordinates of a pair", PairEquivFormula(),
                "For distinct qubits p and q, pairEquiv reads a configuration x of the pair {p, q} as the ordered pair (x(p), x(q)) in Fin 2 x Fin 2.",
                "pairEquiv", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("out-equiv", "Coordinates outside a pair", OutEquivFormula(),
                "When the qubits r and s are exactly the two qubits outside {p, q}, outEquiv reads a configuration z of those qubits as (z(r), z(s)).",
                "outEquiv", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("single-equiv", "Coordinate of one qubit", SingleEquivFormula(),
                "singleEquiv reads a configuration x of the single qubit k as its value x(k) in Fin 2.",
                "singleEquiv", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("out3-equiv", "Coordinates outside one qubit", Out3EquivFormula(),
                "When the qubits r, s and t are exactly the three qubits other than k, out3Equiv reads a configuration z of those qubits as (z(r), z(s), z(t)).",
                "out3Equiv", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("four-equiv", "Coordinates of four qubits", FourEquivFormula(),
                "fourEquiv reads a configuration w of the four qubits as (w(0), w(1), w(2), w(3)).",
                "fourEquiv", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("psi", "The counterexample state", PsiFormula(),
                "The state is (20|0001> + 2|1000> + 6|1011> + |1110>)/21, with norm one since 400 + 4 + 36 + 1 = 441.",
                "psi", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("instrument", "The measurement on qubit A", InstrumentFormula(),
                "The two outcomes are K_0 = diag(21/29, 0) and K_1 = diag(20/29, 1) on qubit A, with K_0^dagger K_0 + K_1^dagger K_1 = I.",
                "instrument", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The residual-correlation sum increases on average", Disp(new Formula.Not(F.Id("claim"))),
                "The outcome K_0 has probability 400/841 and leaves the product state |0001>, so its M is zero. The outcome K_1 has probability 441/841 and leaves (400|0001> + 58|1000> + 174|1011> + 29|1110>)/441. Every two-qubit reduced state of the three states is a real X matrix, with diagonal u, v, r, s in the basis 00, 01, 10, 11, an entry w between 00 and 11 and an entry z between 01 and 10; after reindexing the reduced state and sigma_y x sigma_y to Fin 2 x Fin 2, which keeps the characteristic polynomial, the characteristic polynomial factors as (X^2 - 2(us + w^2)X + (us - w^2)^2)(X^2 - 2(vr + z^2)X + (vr - z^2)^2), with roots (sqrt(us) + |w|)^2, (sqrt(us) - |w|)^2, (sqrt(vr) + |z|)^2 and (sqrt(vr) - |z|)^2, and sorting them gives the concurrence. The concurrences of the pairs AB, AC, AD, BC, BD, CD are (0, 240, 80, 4, 12, 0)/441 for the state and (0, 139200, 46400, 3364, 10092, 0)/194481 for the second outcome; with the linear entropies, M of the state is 7552/194481 and M of the second outcome is 2967747712/37822859361. The average of M after the measurement is 3528832/85766121, which exceeds 7552/194481 by 198400/85766121.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bai-2007-residual-sum-monotone"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("fqr-" + id), DeclarationHandle.Create(Prefix + declaration),
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
        Seq(Parenthesized(Seq(Fin(4), Sp, To, Sp, Fin(2))), Sp, To, Sp, Complex());
    private static Formula QubitMatrix() => Call(F.Id("Matrix"), Fin(2), Fin(2), Complex());
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula ReTr(Formula x) => Call(F.Id("ReTr"), x);
    private static Formula Reduced(Formula set, Formula psi) => Call(F.Id("reducedState"), set, psi);
    private static Formula Singleton(Formula k) => Seq(Esc, OpenBrace, k, Esc, CloseBrace);
    private static Formula PairSet(Formula p, Formula q) =>
        Seq(Esc, OpenBrace, p, Comma, Sp, q, Esc, CloseBrace);
    private static Formula Ket(params byte[] digits) => Seq(Bar, D(digits), Rangle);

    private static Formula Vars(params Formula[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < names.Length; i++)
        {
            if (i > 0)
            {
                parts.Add(Comma);
                parts.Add(Sp);
            }
            parts.Add(names[i]);
        }
        return Seq([.. parts]);
    }

    private static Formula Configs(Formula set) => Parenthesized(Seq(set, Sp, To, Sp, Fin(2)));

    private static Formula Outside(Formula set) => Call(F.Id("Outside"), set);

    private static Formula PairEquivFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q"), x = F.Id("x");
        return Disp(All(Vars(p, q), Fin(4), All(x, Configs(PairSet(p, q)),
            EqTo(Call(F.Id("pairEquiv"), p, q, x), Parenthesized(Vars(Of(x, p), Of(x, q)))))));
    }

    private static Formula OutEquivFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q"), r = F.Id("r"), s = F.Id("s"), z = F.Id("z");
        return Disp(All(Vars(p, q, r, s), Fin(4), All(z, Configs(Outside(PairSet(p, q))),
            EqTo(Call(F.Id("outEquiv"), p, q, r, s, z), Parenthesized(Vars(Of(z, r), Of(z, s)))))));
    }

    private static Formula SingleEquivFormula()
    {
        Formula k = F.Id("k"), x = F.Id("x");
        return Disp(All(k, Fin(4), All(x, Configs(Singleton(k)),
            EqTo(Call(F.Id("singleEquiv"), k, x), Of(x, k)))));
    }

    private static Formula Out3EquivFormula()
    {
        Formula k = F.Id("k"), r = F.Id("r"), s = F.Id("s"), t = F.Id("t"), z = F.Id("z");
        return Disp(All(Vars(k, r, s, t), Fin(4), All(z, Configs(Outside(Singleton(k))),
            EqTo(Call(F.Id("out3Equiv"), k, r, s, t, z),
                Parenthesized(Vars(Of(z, r), Of(z, s), Of(z, t)))))));
    }

    private static Formula FourEquivFormula()
    {
        Formula w = F.Id("w");
        return Disp(All(w, Configs(Fin(4)),
            EqTo(Call(F.Id("fourEquiv"), w),
                Parenthesized(Vars(Of(w, D(0)), Of(w, D(1)), Of(w, D(2)), Of(w, D(3)))))));
    }

    private static Formula TauFormula()
    {
        Formula k = F.Id("k"), psi = Psi;
        Formula rho = Reduced(Singleton(k), psi);
        Formula value = Mul(D(2), Parenthesized(Sub(D(1), ReTr(Mul(rho, rho)))));
        return Disp(All(k, Fin(4), All(psi, Vectors(),
            EqTo(Call(F.Id("linearEntropy"), k, psi), value))));
    }

    private static Formula ConcFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q"), psi = Psi, rho = Rho, l = F.Id("l");
        Formula pair = PairSet(p, q);
        Formula pairStates = Seq(Parenthesized(Seq(pair, Sp, To, Sp, Fin(2))));
        Formula rhoType = Call(F.Id("Matrix"), pairStates, pairStates, Complex());
        Formula product = Mul(rho, Call(F.Id("timeReversed"), pair, rho));
        Formula roots = Call(F.Id("sortDesc"), Call(F.Id("map"), Named(F.Id("re")),
            Call(F.Id("roots"), Call(F.Id("charpoly"), product))));
        Formula difference = Sub(Sub(Sub(Root(Entry(l, 0)), Root(Entry(l, 1))), Root(Entry(l, 2))),
            Root(Entry(l, 3)));
        Formula value = Seq(Max, Parenthesized(Seq(difference, Comma, Sp, D(0))));
        Formula body = Imp(EqTo(rho, Reduced(pair, psi)),
            Imp(EqTo(l, roots), EqTo(Call(F.Id("concurrence"), p, q, psi), value)));
        return Disp(All(p, Fin(4), All(q, Fin(4), All(psi, Vectors(),
            All(rho, rhoType, All(l, Call(F.Id("List"), NumberSet(F.Id("R"))), body))))));
    }

    private static Formula Entry(Formula list, byte i) => Call(F.Id("getD"), list, D(i), D(0));

    private static Formula ResidualFormula()
    {
        Formula k = F.Id("k"), p = F.Id("p"), q = F.Id("q"), psi = Psi;
        Formula entropies = SumOver(k, Call(F.Id("linearEntropy"), k, psi));
        Formula pairs = SumOver(Seq(p, Lt, q), Pow(Call(F.Id("concurrence"), p, q, psi), D(2)));
        return Disp(All(psi, Vectors(),
            EqTo(Call(F.Id("residualSum"), psi), Sub(entropies, Mul(D(2), pairs)))));
    }

    private static Formula ClaimFormula()
    {
        Formula psi = Psi, n = F.Id("n"), k = F.Id("K"), j = F.Id("j"), w = F.Id("w"), p = F.Id("p");
        Formula kj = new Formula.Subscript(k, j);
        Formula pj = new Formula.Subscript(p, j);
        Formula image = Parenthesized(Seq(Call(F.Id("localOp"), D(0), kj), Sp, Cdot, Sp, psi));
        Formula probability = SumOver(w, Pow(Norm(Of(image, w)), D(2)));
        Formula normalized = SumOver(w, Pow(Norm(Of(psi, w)), D(2)));
        Formula complete = EqTo(SumOver(j, Mul(Pow(kj, F.Id("H")), kj)), D(1));
        Formula probabilities = All(j, Call(F.Id("Fin"), n), EqTo(pj, probability));
        Formula outcomes = Seq(j, Sp, Colon, Sp, pj, Sp, Neq, Sp, D(0));
        Formula average = Seq(new Formula.Subscript(Sum, outcomes), Sp,
            Mul(pj, Call(F.Id("residualSum"), Mul(Frac(D(1), Root(pj)), image))));
        Formula weights = Seq(Call(F.Id("Fin"), n), Sp, To, Sp, NumberSet(F.Id("R")));
        Formula body = Imp(EqTo(normalized, D(1)),
            All(n, NumberSet(F.Id("N")), All(k, Seq(Call(F.Id("Fin"), n), Sp, To, Sp, QubitMatrix()),
                Imp(complete, All(p, weights,
                    Imp(probabilities, LeTo(average, Call(F.Id("residualSum"), psi))))))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, All(psi, Vectors(), body)));
    }

    private static Formula PsiFormula()
    {
        Formula sum = Add(Add(Add(Mul(D(2, 0), Ket(0, 0, 0, 1)), Mul(D(2), Ket(1, 0, 0, 0))),
            Mul(D(6), Ket(1, 0, 1, 1))), Ket(1, 1, 1, 0));
        return Disp(EqTo(Psi, Mul(Frac(D(1), D(2, 1)), Parenthesized(sum))));
    }

    private static Formula InstrumentFormula()
    {
        Formula k = F.Id("K");
        Formula first = EqTo(new Formula.Subscript(k, D(0)),
            Call(F.Id("diag"), Frac(D(2, 1), D(2, 9)), D(0)));
        Formula second = EqTo(new Formula.Subscript(k, D(1)),
            Call(F.Id("diag"), Frac(D(2, 0), D(2, 9)), D(1)));
        return Disp(Seq(first, Comma, Qquad, Sp, second));
    }
}
