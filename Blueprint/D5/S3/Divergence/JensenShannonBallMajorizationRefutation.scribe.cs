using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class JensenShannonBallMajorizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/JensenShannonBallMajorizationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/hanson2020entropiccontinuity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-point Jensen-Shannon ball has no majorization-minimizer.",
        H("Jensen-Shannon balls need not have majorization-minimizers"),
        Blocks(
            Paragraph(Text(
                "Vectors are real-valued functions on Fin d, whose indices run from zero to d - 1. "
                    + "A probability vector has nonnegative coordinates and total mass one. "
                    + "For any vector x, x_(j) denotes its j-th largest coordinate, numbered from zero. "
                    + "Thus a sum over j in Fin k is the sum of the k largest coordinates; for k = 0 it is zero.")),
            Node("jensen-shannon", "Jensen-Shannon divergence", JensenShannonFormula(),
                "The divergence uses natural logarithms. Write J(p, q) for the displayed expression. "
                    + "Division by zero is zero. The logarithm is totalized by ln(0) = 0 "
                    + "and ln(x) = ln|x| for nonzero x, "
                    + "so a coordinate of zero contributes zero to its weighted logarithm. "
                    + "If both coordinates are zero, both contributions vanish. "
                    + "Changing between natural and base-two logarithms rescales the divergence by a positive constant.",
                "jensenShannon"),
            Node("majorization-minimizer", "A least element for majorization", MinimizerFormula(),
                "A majorization-minimizer of a set B is a member r of B with r majorized by every q in B. "
                    + "Equation (2.3) expresses this order by descending partial sums: each sum of k largest "
                    + "coordinates of r is at most the corresponding sum for q, for every natural k < d, "
                    + "and the total sums agree. This is the minimum clause of Eq. (3.1). "
                    + "The set B need not consist of probability vectors.",
                "IsMajorizationMinimizer"),
            Node("claim", "The Jensen-Shannon clause of Question 1", ClaimFormula(),
                "For every dimension d, every probability vector p and every positive threshold t, "
                    + "the sublevel set of probability vectors q satisfying J(p, q) <= t has a majorization-minimizer. "
                    + "This is the Jensen-Shannon clause of Chapter 8, Question 1. "
                    + "The square-root Jensen-Shannon metric is sqrt(J(p, q) / ln(2)); "
                    + "its closed ball of radius epsilon > 0 is the displayed sublevel set with "
                    + "t = epsilon^2 ln(2).",
                "claim"),
            Describe.Lean(
                DescribeId.Create("jensen-shannon-ball-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A three-point ball without a majorization-minimizer"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take p = (2/3, 4/15, 1/15), a = (1/2, 2/5, 1/10), "
                            + "b = (8/15, 1/3, 2/15) and t = J(p, a) > 0. All three are probability vectors. "
                            + "For every probability vector r in this ball that is majorized by a, "
                            + "the descending partial sums give 1/10 <= r_i <= 1/2 for every coordinate.")),
                    Paragraph(Text(
                        "The supporting-line inequality for J(p, .) at a gives "
                            + "J(p, r) >= J(p, a) + (1/2) ln(5/7) (r_0 - 1/2), with equality only at r = a. "
                            + "Indeed, its three supporting coefficients are (1/2) ln(6/7), "
                            + "(1/2) ln(6/5) and (1/2) ln(6/5); their sum against r - a reduces to the displayed expression "
                            + "because the coordinates of r and a each sum to one. "
                            + "Since ln(5/7) < 0 and r_0 <= 1/2, membership in the ball forces r = a. "
                            + "Every majorization-minimizer would be majorized by a, which is itself in the ball, "
                            + "and would therefore equal a.")),
                    Paragraph(Text(
                        "However, 60 (J(p, b) - J(p, a)) = ln(4 * 5^55 * 7^35 / 3^144) < 0, "
                            + "since 4 * 5^55 * 7^35 < 3^144. Hence b also belongs to the ball. "
                            + "The two largest coordinates of a sum to 9/10, whereas those of b sum to 13/15. "
                            + "The strict inequality 9/10 > 13/15 shows that a is not majorized by b. "
                            + "Thus this ball has no majorization-minimizer."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hanson-2020-jensen-shannon-ball-majorization-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration) =>
        Describe.Lean(
            DescribeId.Create("jensen-shannon-ball-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Vectors() => Parenthesized(new Formula.TypeArrow(Fin(F.Id("d")), Reals()));
    private static Formula At(Formula vector, Formula index) => new Formula.Subscript(vector, index);
    private static Formula SortedAt(Formula vector, Formula index) => At(vector, Parenthesized(index));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, Parenthesized(body));
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, Parenthesized(body));
    private static Formula SumOver(string variable, Formula size, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(variable), Colon, Sp, Fin(size))), Sp, Parenthesized(body));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula ProbabilityFormula(Formula vector) =>
        And(All("i", Fin(F.Id("d")), LE(D(0), At(vector, F.Id("i")))),
            Equal(SumOver("i", F.Id("d"), At(vector, F.Id("i"))), D(1)));

    private static Formula MajorizationFormula(Formula left, Formula right)
    {
        Formula PartialSum(Formula vector, Formula size) =>
            SumOver("j", size, SortedAt(vector, F.Id("j")));
        return And(All("k", Naturals(), Imp(LT(F.Id("k"), F.Id("d")),
                LE(PartialSum(left, F.Id("k")), PartialSum(right, F.Id("k"))))),
            Equal(PartialSum(left, F.Id("d")), PartialSum(right, F.Id("d"))));
    }

    private static Formula JensenShannonFormula()
    {
        Formula x = At(F.Id("p"), F.Id("i")), y = At(F.Id("q"), F.Id("i"));
        Formula denominator = Add(x, y);
        Formula summand = Add(
            Multiply(x, Call("ln", new Formula.Fraction(Multiply(D(2), x), denominator))),
            Multiply(y, Call("ln", new Formula.Fraction(Multiply(D(2), y), denominator))));
        return All("d", Naturals(), All("p", Vectors(), All("q", Vectors(),
            Equal(Call("jensenShannon", F.Id("p"), F.Id("q")),
                Multiply(new Formula.Fraction(D(1), D(2)), SumOver("i", F.Id("d"), summand))))));
    }

    private static Formula MinimizerFormula() =>
        All("d", Naturals(), All("B", Call("Set", Vectors()), All("r", Vectors(),
            IffOf(Call("IsMajorizationMinimizer", F.Id("B"), F.Id("r")),
                And(Member(F.Id("r"), F.Id("B")), All("q", Vectors(),
                    Imp(Member(F.Id("q"), F.Id("B")), MajorizationFormula(F.Id("r"), F.Id("q")))))))));

    private static Formula ClaimFormula()
    {
        Formula ball = Seq(OpenBrace, F.Id("q"), Colon, Sp, Vectors(), Sp, Mid, Sp,
            And(ProbabilityFormula(F.Id("q")),
                LE(Call("jensenShannon", F.Id("p"), F.Id("q")), F.Id("t"))), CloseBrace);
        return IffOf(Named("claim"), All("d", Naturals(), All("p", Vectors(),
            Imp(ProbabilityFormula(F.Id("p")), All("t", Reals(), Imp(LT(D(0), F.Id("t")),
                Some("r", Vectors(), Call("IsMajorizationMinimizer", ball, F.Id("r")))))))));
    }
}
