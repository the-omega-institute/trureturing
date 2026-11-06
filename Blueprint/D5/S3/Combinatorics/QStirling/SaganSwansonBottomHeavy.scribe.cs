using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QStirling;

internal sealed class SaganSwansonBottomHeavyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/sagan2022qstirling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All four unshifted unsigned q-Stirling families have bottom-heavy coefficients.",
        H("Bottom heaviness of q-Stirling coefficients"),
        Blocks(
            Node("second-kind-a", "Type A, second kind", "S", Recurrence("S", true, false),
                "Section 1.1, equation (2), printed page 3: “We will call the (type A) "
                    + "q-Stirling numbers of the second kind the polynomials S[n, k] in the "
                    + "variable q obtained by replacing (1) with S[n,k] = S[n−1,k−1]+[k] S[n−1,k].” "
                    + "The initial row is the Kronecker delta at zero. Here n ranges over Nat, "
                    + "k over Int, and the polynomial variable is Polynomial.X over Nat. "
                    + "Negative k gives zero. The existing qInteger is the sum of X^j for j < a.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("first-kind-a", "Type A, first kind", "c", Recurrence("c", false, false),
                "Section 1.1, equation (5), printed page 4: “The (signless, type A) q-Stirling "
                    + "numbers of the first kind are the polynomials c[n, k] obtained by "
                    + "replacing (4) with c[n,k]=c[n−1,k−1]+[n−1] c[n−1,k].” "
                    + "The initial row is the Kronecker delta at zero. The displayed successor "
                    + "row has multiplier qInteger n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("second-kind-b", "Type B, second kind", "SB", Recurrence("SB", true, true),
                "Definition 1.5, equation (8), printed page 6: “The type B q-Stirling numbers "
                    + "of the second kind are defined by replacing (1) with "
                    + "S_B[n,k]= S_B[n−1,k−1]+ [2k+1] S_B[n−1,k].” "
                    + "SB is the Lean name of S_B. The initial row is the Kronecker delta at "
                    + "zero, and negative k gives zero. Int.toNat is applied only in the "
                    + "nonnegative branch.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("first-kind-b", "Type B, first kind", "cB", Recurrence("cB", false, true),
                "Definition 1.5, equation (9), printed page 6: “The (signless) type B Stirling "
                    + "numbers of the first kind are defined by replacing (4) with "
                    + "c_B[n,k] = c_B[n−1,k−1] + [2n−1] c_B[n−1,k].” "
                    + "cB is the Lean name of c_B. Its successor-row multiplier is "
                    + "qInteger (2*n+1), and its initial row is the Kronecker delta at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bottom-heavy-claim", "Conjecture 7.6", "claim",
                Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, ClaimBody())),
                "Conjecture 7.6, printed page 40: “For each n, k, the coefficients of "
                    + "S[n, k], c[n, k], S_B[n, k], and c_B[n, k] are all bottom heavy.” "
                    + "Section 7.5, printed page 39: “A sequence is bottom heavy if aₖ ≥ aₙ₋ₖ "
                    + "for k < n/2.” The list starts at exponent zero and ends at the actual "
                    + "degree. In the formula, n : Nat and k : Int select a row entry; p is "
                    + "any of the four polynomials; r : Nat satisfies the strict-half test "
                    + "2*r < Polynomial.natDegree p. Natural subtraction then gives the "
                    + "reflected exponent. Zero and constant polynomials have no such r. "
                    + "The separately shifted S-bar family is outside this assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("all-four-bottom-heavy", "All four families are bottom heavy", "result",
                Disp(ClaimBody()),
                "Products of positive-length qInteger polynomials decompose into sums of "
                    + "centered interval layers. These layers are symmetric, have bounded "
                    + "support, and their coefficients rise toward the center. An atom with "
                    + "positive constant coefficient can therefore be compared at every "
                    + "ambient degree bounding its support. Nonnegative sums preserve this "
                    + "comparison at the degree of the whole sum, even when their summands "
                    + "have different degrees. The four recurrences preserve this class, "
                    + "which proves the stated inequality for every integer k. This does "
                    + "not assert unimodality or log-concavity of the resulting sums.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula PolynomialNat() => App(F.Id("Polynomial"), Nat());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] arguments) =>
        Seq([function, .. arguments.Select(argument => Seq(Sp, Parenthesized(argument)))]);
    private static Formula Qualified(params string[] names) =>
        Seq(Operatorname, Grp(Seq([.. names.SelectMany((name, i) =>
            i == 0 ? new Formula[] { F.Id(name) } : [Dot, F.Id(name)])])));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Degree(Formula p) => App(Qualified("Polynomial", "natDegree"), p);
    private static Formula Coeff(Formula p, Formula r) => App(Qualified("Polynomial", "coeff"), p, r);
    private static Formula QInteger(Formula a) => App(Qualified("D5", "S0", "Certificates",
        "Polynomials", "QProductNecessityRefutation", "qInteger"), a);
    private static Formula Initial(Formula k) => Call("ite", Equal(k, D(0)), D(1), D(0));

    private static Formula Recurrence(string name, bool secondKind, bool typeB)
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var index = secondKind ? k : n;
        var length = typeB ? Add(Multiply(D(2), index), D(1)) : index;
        if (secondKind) length = App(Qualified("Int", "toNat"), length);
        var rhs = Add(Call(name, n, Subtract(k, D(1))),
            Multiply(QInteger(length), Call(name, n, k)));
        if (secondKind) rhs = Call("ite", Rel(k, FormulaRelationOperator.LessThan, D(0)), D(0), rhs);
        return Disp(All("n", Nat(), All("k", Int(),
            Logic(Equal(Call(name, D(0), k), Initial(k)), FormulaLogicOperator.And,
                Equal(Call(name, Add(n, D(1)), k), rhs)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var p = F.Id("p");
        var r = F.Id("r");
        var selected = Logic(Equal(p, Call("S", n, k)), FormulaLogicOperator.Or,
            Logic(Equal(p, Call("c", n, k)), FormulaLogicOperator.Or,
                Logic(Equal(p, Call("SB", n, k)), FormulaLogicOperator.Or,
                    Equal(p, Call("cB", n, k)))));
        return All("n", Nat(), All("k", Int(), All("p", PolynomialNat(),
            Logic(selected, FormulaLogicOperator.Implies,
                All("r", Nat(), Logic(Rel(Multiply(D(2), r), FormulaRelationOperator.LessThan,
                    Degree(p)), FormulaLogicOperator.Implies,
                    Rel(Coeff(p, Subtract(Degree(p), r)), FormulaRelationOperator.LessThanOrEqual,
                        Coeff(p, r))))))));
    }
}
