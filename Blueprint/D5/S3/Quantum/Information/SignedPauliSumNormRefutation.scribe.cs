using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SignedPauliSumNormRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SignedPauliSumNormRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/liabotro2017improved");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For three qubits, one choice of signs makes the signed sum of all 63 non-identity Pauli words an operator with eigenvalue 21, hence of norm at least 21, above (sqrt(3) + 1)^3 - 1 = 9 + 6 sqrt(3). This refutes the conjecture of O. Liabotro (arXiv:1607.02667, Eq. (78)) that every such signed sum on m qubits has norm at most (sqrt(3) + 1)^m - 1.",
        H("The signed Pauli sum bound fails for three qubits"),
        Blocks(
            Node("digit", "Pauli labels of base-4 digits", DigitFormula(),
                "The Pauli label of a base-4 digit c: sigma~_0 = I, sigma~_1 = X, sigma~_2 = Y and sigma~_3 = Z.",
                "sigmaOfDigit", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sum", "Signed sums of Pauli words", SumFormula(),
                "For a sign function beta on the indices k, the sum over k = 1, ..., 4^m - 1 of (-1)^beta(k) times the word operator wordOp(g_k) = P_(g_k(0)) tensor ... tensor P_(g_k(m-1)), where g_k(i) = sigmaOfDigit(floor(k / 4^i) mod 4) is the Pauli label of the base-4 digit of k at qubit i and P_I = I, P_X = X, P_Y = iXZ, P_Z = Z are the Pauli matrices. This is the matrix Sigma(beta) of the paper, with c_(i+1)(k) the digit at qubit i.",
                "signedPauliSum", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured norm bound", ClaimFormula(),
                "The conjecture of the paper: for every number m of qubits and every sign function beta on the natural numbers (only its values at k = 1, ..., 4^m - 1 enter), the operator norm of Sigma(beta) is at most (sqrt(3) + 1)^m - 1. The norm is the operator norm for the Euclidean norm on C^(2^m). The paper checks m = 1 and m = 2 exhaustively.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjectured bound fails for three qubits",
                Disp(new Formula.Not(F.Id("claim"))),
                "Take m = 3 and v = (-1 + 2i, 1, 1, 1, 1, 1, 1, 1), the first coordinate being the all-zero basis label. For every non-identity word P the number <v, P v> is 4 or -4; choose beta(k) = 0 when it is 4 for the word P whose letters are the base-4 digits of k, and beta(k) = 1 otherwise; the digits of k = 1, ..., 63 run once over the 63 non-identity words. A kernel-checked computation over the Gaussian integers gives Sigma(beta) v = 21 v, and the ring map from the Gaussian integers to C carries it to the complex matrices. Since v is nonzero and the operator norm bounds |Sigma(beta) v| by the norm times |v|, the norm of Sigma(beta) is at least 21. On the other side (sqrt(3) + 1)^3 - 1 = 9 + 6 sqrt(3) < 21 because sqrt(3) < 2, so the conjectured bound fails for m = 3.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("liabotro-2017-signed-pauli-sum-norm"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("paulisum-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinOf(Formula n) => Call(F.Id("Fin"), n);

    private static Formula DigitFormula()
    {
        Formula c = F.Id("c");
        Formula cases = Seq(Call(F.Id("sigmaOfDigit"), D(0)), Sp, Eq, Sp, F.Id("I"), Comma, Sp,
            Call(F.Id("sigmaOfDigit"), D(1)), Sp, Eq, Sp, F.Id("X"), Comma, Sp,
            Call(F.Id("sigmaOfDigit"), D(2)), Sp, Eq, Sp, F.Id("Y"), Comma, Sp,
            Call(F.Id("sigmaOfDigit"), c), Sp, Eq, Sp, F.Id("Z"), Comma, Sp,
            Rel(c, FormulaRelationOperator.GreaterThanOrEqual, D(3)));
        return Disp(cases);
    }

    private static Formula SumFormula()
    {
        Formula beta = Beta, k = F.Id("k"), i = F.Id("i");
        Formula digit = Call(F.Id("sigmaOfDigit"),
            Seq(Lfloor, new Formula.Fraction(k, new Formula.Power(D(4), i)), Rfloor, Sp, Mathrm, Grp(F.Id("mod")), Sp, D(4)));
        Formula word = Call(F.Id("wordOp"), Seq(i, Sp, Mapsto, Sp, digit));
        Formula sign = new Formula.Power(Parenthesized(new Formula.Negate(D(1))),
            new Formula.Apply(beta, [k]));
        Formula term = new Formula.Binary(sign, FormulaBinaryOperator.Multiply, word);
        Formula range = Seq(Underscore, Grp(k, Sp, Eq, Sp, D(1)), Caret,
            Grp(new Formula.Binary(new Formula.Power(D(4), F.Id("m")), FormulaBinaryOperator.Subtract, D(1))));
        Formula sum = Seq(Sum, range, Sp, term);
        return Disp(Equal(Call(F.Id("signedPauliSum"), beta), sum));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), beta = Beta;
        Formula betaType = Seq(Naturals(), Sp, To, Sp, FinOf(D(2)));
        Formula bound = Rel(new Formula.Norm(Call(F.Id("signedPauliSum"), beta)),
            FormulaRelationOperator.LessThanOrEqual,
            new Formula.Binary(
                new Formula.Power(Parenthesized(new Formula.Binary(Seq(Sqrt, Grp(D(3))),
                    FormulaBinaryOperator.Add, D(1))), m),
                FormulaBinaryOperator.Subtract, D(1)));
        Formula body = All("m", Naturals(),
            Seq(Forall, Sp, beta, Sp, Colon, Sp, betaType, Comma, Sp, bound));
        return Disp(Iff(F.Id("claim"), body));
    }
}
