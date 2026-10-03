using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TwoQubitBinegativityUpperBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/girard2017binegativity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Girard and Gour (arXiv:1701.02724) conjecture that the binegativity of every two-qubit state is at most nu (c + nu)^2 / (2 (c^2 + nu^2)), where nu is the negativity and c the concurrence. The upper bound fails: the rank-two state (|v><v| + 9 |00><00|)/26 with v = (3, 2, 2, 0) has negativity 2/13, concurrence at least 4/13 and binegativity 1/7, while the bound is at most 9/65.",
        H("The upper binegativity bound of Girard and Gour fails"),
        Blocks(
            Node("bineg", "Binegativity", BinegFormula(),
                "For a two-qubit matrix sigma, sigma^Gamma is the partial transposition on the second qubit (the existing partialTransposeB at d = 2) and X_- is the negative part of a self-adjoint matrix X, so that X = X_+ - X_- with X_+ and X_- positive semidefinite and X_+ X_- = 0 (Mathlib's negative part). The binegativity is Tr[(sigma^Gamma)_-] + 2 Tr[(((sigma^Gamma)_-)^Gamma)_-]. The negativity N(sigma) = 2 Tr[(sigma^Gamma)_-] is the existing negativity at d = 2, twice the sum of the absolute values of the negative eigenvalues of sigma^Gamma.",
                "binegativity", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pure", "Concurrence of a pure state", PureFormula(),
                "For a unit vector psi of two qubits, the concurrence is 2 |psi_00 psi_11 - psi_01 psi_10|.",
                "pureConcurrence", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conc", "Concurrence", ConcFormula(),
                "The concurrence of a two-qubit state is the infimum of sum_i p_i C(psi_i) over the decompositions sigma = sum_i p_i |psi_i><psi_i| into finitely many unit vectors psi_i with nonnegative weights p_i.",
                "concurrence", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured upper bound", ClaimFormula(),
                "The paper conjectures that nu (c + nu)(nu + 1)/((c + nu)^2 + 2c(1 - c)) <= N_2(sigma) <= (nu/2)(c + nu)^2/(c^2 + nu^2) for all states sigma with fixed negativity N(sigma) = nu and concurrence C(sigma) = c. The displayed statement is the upper inequality for every density matrix with positive negativity, which excludes the quotient 0/0 on separable states.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("witness", "The counterexample state", WitnessFormula(),
                "The state is the mixture of |v><v|/17 with weight 17/26, v = (3, 2, 2, 0) in the basis 00, 01, 10, 11, and of |00><00| with weight 9/26. It is positive semidefinite with trace one.",
                "witness", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The upper bound fails", Disp(new Formula.Not(F.Id("claim"))),
                "Let A be the partial transpose of the state. With w = (-1, 1, 1, 2), A = (A + ww^T/91) - ww^T/91, where A + ww^T/91 is a sum of three positive rank-one terms with rational coefficients and annihilates w, so the uniqueness of the positive and negative parts gives A_- = ww^T/91, of trace 1/13. In the same way, with z = (2, 3, 3, -2), the negative part of (A_-)^Gamma is 3zz^T/2366, of trace 3/91. Hence the binegativity is 1/13 + 6/91 = 1/7. The trace of A_- is also the sum of the negative parts of the eigenvalues of A, so the negativity is 2/13. In every decomposition of the state into pure states, the zero entry at 11,11 forces every vector with positive weight to have zero 11 amplitude, so its concurrence is 2 |psi_01 psi_10| and the triangle inequality gives a total of at least 2 |rho_(01,10)| = 4/13; the rational decomposition with weights 9/13, 1/26, 7/26 and vectors (-7, -4, -4, 0)/9, (1, -2, -2, 0)/3 and (1, 0, 0, 0) shows that the infimum is taken over a nonempty set. For nu = 2/13 the bound (nu/2)(c + nu)^2/(c^2 + nu^2) is at most 9/65 when c >= 4/13, because 9(c^2 + nu^2) - 5(c + nu)^2 = 2(2c - nu)(c - 2nu) >= 0, and 9/65 < 1/7.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("girard-2017-binegativity-upper-bound"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("tqb-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Abs(Formula x) => new Formula.Absolute(x);
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Nat() => NumberSet(F.Id("N"));
    private static Formula Real() => NumberSet(F.Id("R"));
    private static Formula TwoQubit() => F.Id("TwoQubit");
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula Labels() =>
        Seq(Call(F.Id("Fin"), D(2)), Sp, F.Times, Sp, Call(F.Id("Fin"), D(2)), Sp, To, Sp,
            NumberSet(F.Id("C")));
    private static Formula ReTr(Formula x) => Call(F.Id("ReTr"), x);
    private static Formula NegPart(Formula x) => Call(F.Id("negPart"), x);
    private static Formula Pt(Formula x) => Call(F.Id("partialTransposeB"), x);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Entry(Formula psi, Formula a, Formula b) => Call(psi, Pair(a, b));
    private static Formula Neg2(Formula sigma) => Call(F.Id("negativity"), D(2), sigma);
    private static Formula Conc(Formula sigma) => Call(F.Id("concurrence"), sigma);

    private static Formula BinegFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula first = NegPart(Pt(sigma));
        Formula value = Add(ReTr(first), Mul(D(2), ReTr(NegPart(Pt(first)))));
        return Disp(All(sigma, TwoQubit(), EqTo(Call(F.Id("binegativity"), sigma), value)));
    }

    private static Formula PureFormula()
    {
        Formula psi = F.Id("psi");
        Formula det = Sub(Mul(Entry(psi, D(0), D(0)), Entry(psi, D(1), D(1))),
            Mul(Entry(psi, D(0), D(1)), Entry(psi, D(1), D(0))));
        Formula vectors = Labels();
        return Disp(All(psi, vectors,
            EqTo(Call(F.Id("pureConcurrence"), psi), Mul(D(2), Abs(det)))));
    }

    private static Formula ConcFormula()
    {
        Formula sigma = F.Id("sigma"), s = F.Id("s"), k = F.Id("k"), p = F.Id("p"),
            psi = F.Id("psi"), i = F.Id("i"), x = F.Id("x");
        Formula pi = Call(p, i), psii = Call(psi, i);
        Formula decomposition = EqTo(sigma, SumOver(i, Mul(pi,
            Call(F.Id("vecMulVec"), psii, Call(F.Id("star"), psii)))));
        Formula unit = All(i, Call(F.Id("Fin"), k),
            EqTo(SumOver(x, Pow(Abs(Call(psii, x)), D(2))), D(1)));
        Formula weights = All(i, Call(F.Id("Fin"), k), LeTo(D(0), pi));
        Formula value = EqTo(s, SumOver(i, Mul(pi, Call(F.Id("pureConcurrence"), psii))));
        Formula condition = Some(k, Nat(), Some(p, Seq(Call(F.Id("Fin"), k), Sp, To, Sp, Real()),
            Some(psi, Seq(Call(F.Id("Fin"), k), Sp, To, Sp, Labels()),
                And(weights, And(unit, And(decomposition, value))))));
        Formula set = Seq(Esc, OpenBrace, s, Sp, Mid, Sp, condition, Esc, CloseBrace);
        return Disp(All(sigma, TwoQubit(), EqTo(Conc(sigma), Call(F.Id("sInf"), set))));
    }

    private static Formula ClaimFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula nu = Neg2(sigma), c = Conc(sigma);
        Formula bound = Mul(Frac(nu, D(2)),
            Frac(Pow(Parenthesized(Add(c, nu)), D(2)), Add(Pow(c, D(2)), Pow(nu, D(2)))));
        Formula body = Imp(Call(F.Id("IsDensity"), sigma),
            Imp(LtTo(D(0), nu), LeTo(Call(F.Id("binegativity"), sigma), bound)));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, All(sigma, TwoQubit(), body)));
    }

    private static Formula WitnessFormula()
    {
        Formula v = Call(F.Id("vec4"), D(3), D(2), D(2), D(0));
        Formula e = Call(F.Id("vec4"), D(1), D(0), D(0), D(0));
        Formula vv = Call(F.Id("vecMulVec"), v, Call(F.Id("star"), v));
        Formula ee = Call(F.Id("vecMulVec"), e, Call(F.Id("star"), e));
        return Disp(EqTo(F.Id("witness"),
            Mul(Frac(D(1), D(2, 6)), Parenthesized(Add(vv, Mul(D(9), ee))))));
    }
}
