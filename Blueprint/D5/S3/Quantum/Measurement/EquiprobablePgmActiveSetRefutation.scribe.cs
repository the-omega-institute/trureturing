using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EquiprobablePgmActiveSetRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/cha2026structural");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cha and Lee (arXiv:2507.05778, Quantum Information Processing 25, 310) compare two upper bounds on the optimal success probability of minimum-error state discrimination, one built from the pretty good measurement on all states and one built from it on the active set I_+ of labels with nonzero optimal effects. For equal priors they conjecture (|I_+| - 1)(P^PGM_+ - 1/N) <= (N - 1)(P^PGM - 1/N). Three positive definite qubit states with rational entries violate it.",
        H("The equiprobable pretty-good-measurement comparison of Cha and Lee fails"),
        Blocks(
            Node("success", "The success probability", SuccessFormula(),
                "For the equiprobable ensemble sigma_i = rho_i / N, the success probability of the POVM E is sum_i tr(sigma_i E_i); the real part reads this real trace.",
                "success", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pgm-score", "The pretty good measurement on a set of labels", PgmScoreFormula(),
                "For a set A of labels, S_A = sum_{j in A} sigma_j and the pretty good measurement has effects S_A^{-1/2} sigma_i S_A^{-1/2} for i in A; its score keeps the original weights sigma_i = rho_i / N. S_A^{-1/2} is the continuous-functional-calculus power. With A all labels this is P^PGM; with A = I_+ it is P^PGM_+.",
                "pgmScore", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured comparison", ClaimFormula(),
                "Journal Eq. (18) for equal priors, with I_+ the set of labels whose optimal effect is nonzero. POVMs are the frozen finitePOVM: positive semidefinite effects on C^(k+1) that sum to the identity. The encoding asks for some optimal POVM, the weakest reading of the optimal POVM, and restricts to N >= 1 positive definite states, for which every nonempty S_A is invertible.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rho", "The three states", RhoFormula(),
                "Three positive definite qubit density matrices with rational entries; mat(a, b, c, e) is the 2 x 2 matrix with rows (a, b) and (c, e).",
                "rho", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The comparison fails for three qubit states", Disp(new Formula.Not(F.Id("claim"))),
                "Take N = 3, d = 2 and sigma_i = rho_i / 3. The matrix Gamma = diag(418, 19)/1203 has Gamma - sigma_1 = (6/401)(1, -1)(1, -1)^T, Gamma - sigma_2 = (6/401)(1, 1)(1, 1)^T and Gamma - sigma_3 = diag(1011, 453)/48922, all positive semidefinite. Hence every POVM satisfies sum_i tr(sigma_i E_i) = tr(Gamma) - sum_i tr((Gamma - sigma_i) E_i) <= tr(Gamma) = 437/1203, and the projectors (1/2)(1, 1)(1, 1)^T, (1/2)(1, -1)(1, -1)^T with E_3 = 0 attain it. For an optimal POVM every term tr((Gamma - sigma_i) E_i) vanishes. Since Gamma - sigma_3 is at least (453/48922) I, E_3 = 0; and E_1 = 0 or E_2 = 0 would leave tr(Gamma - sigma_j) = 12/401. So I_+ = {1, 2}. Then S = diag(121, 1)/122 and S_+ = diag(800, 2)/1203, whose inverse square roots are diagonal; P^PGM = 20192347/58370763 and P^PGM_+ = 2167/6015, and (2 - 1)(P^PGM_+ - 1/3) - (3 - 1)(P^PGM - 1/3) = 168714/97284605 > 0.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cha-2026-equiprobable-pgm-active-set"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("eqpgm-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Real() => NumberSet(F.Id("R"));
    private static Formula Complex() => NumberSet(F.Id("C"));
    private static Formula Nat() => NumberSet(F.Id("N"));
    private static Formula Fin(Formula n) => Call(F.Id("Fin"), n);
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Mat(Formula d) => Call(F.Id("Matrix"), Fin(d), Fin(d), Complex());
    private static Formula Families(Formula n, Formula d) => Arrow(Fin(n), Mat(d));
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
    private static Formula SumOver(Formula index, Formula body) => Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula Tr(Formula x) => Call(F.Id("tr"), x);
    private static Formula Re(Formula x) => Call(F.Id("Re"), x);
    private static Formula Weighted(Formula rho, Formula i) => Mul(Frac(D(1), F.Id("N")), Of(rho, i));
    private static Formula Matrix2(Formula a, Formula b, Formula c, Formula e) =>
        Call(F.Id("mat"), a, b, c, e);
    private static Formula Q(byte[] num, byte[] den) => Frac(D(num), D(den));

    private static Formula SuccessFormula()
    {
        Formula d = F.Id("d"), n = F.Id("N"), rho = F.Id("rho"), e = F.Id("E"), i = F.Id("i");
        Formula value = SumOver(Seq(i, Sp, InMacro, Sp, Fin(n)), Re(Tr(Mul(Weighted(rho, i), Of(e, i)))));
        return Disp(All(Vars(d, n), Nat(), All(Vars(rho, e), Families(n, d),
            EqTo(Call(F.Id("success"), rho, e), value))));
    }

    private static Formula PgmScoreFormula()
    {
        Formula d = F.Id("d"), n = F.Id("N"), rho = F.Id("rho"), a = F.Id("A"), i = F.Id("i"), j = F.Id("j");
        Formula s = Pow(Parenthesized(SumOver(Seq(j, Sp, InMacro, Sp, a), Weighted(rho, j))),
            Seq(Minus, Frac(D(1), D(2))));
        Formula term = Re(Tr(Mul(Mul(Mul(Weighted(rho, i), s), Weighted(rho, i)), s)));
        Formula value = SumOver(Seq(i, Sp, InMacro, Sp, a), term);
        return Disp(All(Vars(d, n), Nat(), All(rho, Families(n, d), All(a, Call(F.Id("Finset"), Fin(n)),
            EqTo(Call(F.Id("pgmScore"), rho, a), value)))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), n = F.Id("N"), rho = F.Id("rho"), e = F.Id("E"), f = F.Id("F"), i = F.Id("i"),
            a = F.Id("A");
        Formula dim = Add(k, D(1));
        Formula states = And(All(i, Fin(n), Call(F.Id("PosDef"), Of(rho, i))),
            All(i, Fin(n), EqTo(Tr(Of(rho, i)), D(1))));
        Formula optimal = All(f, Families(n, dim), Imp(Call(F.Id("finitePOVM"), f),
            LeTo(Call(F.Id("success"), rho, f), Call(F.Id("success"), rho, e))));
        Formula active = EqTo(a, Seq(Esc, OpenBrace, i, Sp, Mid, Sp,
            Rel(Of(e, i), FormulaRelationOperator.NotEqual, D(0)), Esc, CloseBrace));
        Formula comparison = LeTo(
            Mul(Parenthesized(Sub(Seq(Bar, a, Bar), D(1))),
                Parenthesized(Sub(Call(F.Id("pgmScore"), rho, a), Frac(D(1), n)))),
            Mul(Parenthesized(Sub(n, D(1))),
                Parenthesized(Sub(Call(F.Id("pgmScore"), rho, Call(F.Id("univ"), Fin(n))), Frac(D(1), n)))));
        Formula body = Imp(Rel(D(0), FormulaRelationOperator.LessThan, n), Imp(states,
            Some(e, Families(n, dim), And(And(Call(F.Id("finitePOVM"), e), optimal),
                All(a, Call(F.Id("Finset"), Fin(n)), Imp(active, comparison))))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All(Vars(k, n), Nat(), All(rho, Families(n, dim), body))));
    }

    private static Formula RhoFormula()
    {
        Formula rho = F.Id("rho");
        Formula r0 = EqTo(Of(rho, D(0)), Matrix2(Q([4, 0, 0], [4, 0, 1]), Q([1, 8], [4, 0, 1]),
            Q([1, 8], [4, 0, 1]), Q([1], [4, 0, 1])));
        Formula r1 = EqTo(Of(rho, D(1)), Matrix2(Q([4, 0, 0], [4, 0, 1]), Seq(Minus, Q([1, 8], [4, 0, 1])),
            Seq(Minus, Q([1, 8], [4, 0, 1])), Q([1], [4, 0, 1])));
        Formula r2 = EqTo(Of(rho, D(2)), Matrix2(Q([4, 7, 9, 6, 3], [4, 8, 9, 2, 2]), D(0),
            D(0), Q([9, 5, 9], [4, 8, 9, 2, 2])));
        return Disp(And(And(r0, r1), r2));
    }
}
