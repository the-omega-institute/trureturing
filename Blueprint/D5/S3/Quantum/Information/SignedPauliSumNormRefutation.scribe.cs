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
            Node("sum", "Signed sums of Pauli words", SumFormula(),
                "For a sign function beta on the Pauli words g of m qubits, the sum over all words other than the identity word I (the word whose every letter is I) of (-1)^beta(g) times the word operator wordOp(g) = P_(g_1) tensor ... tensor P_(g_m), where P_I = I, P_X = X, P_Y = iXZ and P_Z = Z are the Pauli matrices. This is the matrix Sigma(beta) of the paper, whose index k runs over the base-4 digit strings of 1, ..., 4^m - 1, that is, over the non-identity words.",
                "signedPauliSum", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured norm bound", ClaimFormula(),
                "The conjecture of the paper: for every number m of qubits and every sign function beta, the operator norm of Sigma(beta) is at most (sqrt(3) + 1)^m - 1. The norm is the operator norm for the Euclidean norm on C^(2^m). The paper checks m = 1 and m = 2 exhaustively.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjectured bound fails for three qubits",
                Disp(new Formula.Not(F.Id("claim"))),
                "Take m = 3 and v = (-1 + 2i, 1, 1, 1, 1, 1, 1, 1), the first coordinate being the all-zero basis label. For every non-identity word P the number <v, P v> is 4 or -4; choose beta(P) = 0 when it is 4 and beta(P) = 1 otherwise. A kernel-checked computation over the Gaussian integers gives Sigma(beta) v = 21 v, and the ring map from the Gaussian integers to C carries it to the complex matrices. Since v is nonzero and the operator norm bounds |Sigma(beta) v| by the norm times |v|, the norm of Sigma(beta) is at least 21. On the other side (sqrt(3) + 1)^3 - 1 = 9 + 6 sqrt(3) < 21 because sqrt(3) < 2, so the conjectured bound fails for m = 3.",
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
    private static Formula WordType(Formula m) => Seq(FinOf(m), Sp, To, Sp, F.Id("Pauli"));

    private static Formula SumFormula()
    {
        Formula beta = Beta, g = F.Id("g");
        Formula identityWord = Seq(Mathbf, Grp(F.Id("I")));
        Formula index = Seq(g, Sp, Colon, Sp, WordType(F.Id("m")), Comma, Sp,
            Rel(g, FormulaRelationOperator.NotEqual, identityWord));
        Formula sign = new Formula.Power(Parenthesized(new Formula.Negate(D(1))),
            new Formula.Apply(beta, [g]));
        Formula term = new Formula.Binary(sign, FormulaBinaryOperator.Multiply,
            Call(F.Id("wordOp"), g));
        Formula sum = Seq(new Formula.Subscript(Sum, index), Sp, term);
        return Disp(Equal(Call(F.Id("signedPauliSum"), beta), sum));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), beta = Beta;
        Formula betaType = Seq(Parenthesized(WordType(m)), Sp, To, Sp, FinOf(D(2)));
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
