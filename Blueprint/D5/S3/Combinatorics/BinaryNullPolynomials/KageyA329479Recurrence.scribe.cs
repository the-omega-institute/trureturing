using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinaryNullPolynomials;

internal sealed class KageyA329479RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/kagey2019a329479");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary integer polynomials of each positive degree that vanish modulo three "
            + "at every integer satisfy Kagey's order-eight counting recurrence. "
            + "Coefficient words identify the count with a nine-state transfer column; "
            + "an exact column identity propagates through every matrix power.",
        H("Kagey's Binary Null Polynomial Recurrence"),
        Blocks(
            Node("polynomial-count", "The polynomial count", "a", CountFormula(),
                "OEIS A329479, revision 25, NAME (unpaginated): \"Number of degree n "
                    + "polynomials f with all nonzero coefficients equal to 1 such that f(k) "
                    + "is divisible by 3 for all integers k.\" The carrier is Polynomial Int, "
                    + "so distinct integer polynomials are counted separately. Degree is "
                    + "exactly n, monicness forces the leading coefficient to be one, and "
                    + "every coefficient is zero or one. The degree-seven example fixes the "
                    + "degree interpretation despite the entry's different string-length wording.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("recurrence-claim", "The conjectured recurrence", "claim",
                Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody()))),
                "OEIS A329479, revision 25, final FORMULA line (unpaginated): "
                    + "\"Conjectured recurrence: a(n) = 2a(n-1) + 2a(n-2) - 5a(n-3) - 2a(n-4) "
                    + "+ 10a(n-5) - 4a(n-6) - 4a(n-7) + 8a(n-8).\" The offset is one, "
                    + "so nine is the first argument whose eight predecessors are all in the "
                    + "sequence. Indices use natural subtraction; counts are cast to Int "
                    + "before the additions, multiplications and subtractions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("recurrence-proof", "The recurrence holds", "result", Disp(ClaimBody()),
                "Evaluation at zero forces the constant coefficient to vanish. A polynomial "
                    + "of degree n plus one is recovered uniquely from its n interior Boolean "
                    + "coefficients and its leading one. Over ZMod 3 its remaining null "
                    + "condition is simultaneous vanishing at one and minus one. Prepending "
                    + "a Boolean coefficient changes the two evaluations by affine maps on "
                    + "ZMod 3 times ZMod 3. The labelled-word transfer identity equates the "
                    + "polynomial count to the column ending at the evaluation pair of X. "
                    + "Direct arithmetic verifies the degree-eight identity at all nine "
                    + "starting states. The transition is linear, so induction propagates "
                    + "that identity to every power. The coefficient-word correspondence "
                    + "then gives the claimed recurrence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("kag329479-binarynull"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Natural => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Integer => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        Seq(function, Sp, Join(arguments));
    private static Formula Call(string name, params Formula[] arguments) => App(V(name), arguments);
    private static Formula Join(Formula[] arguments) =>
        Seq(arguments.SelectMany((argument, index) => index == 0
            ? new[] { Parenthesized(argument) }
            : new[] { Sp, Parenthesized(argument) }).ToArray());
    private static Formula All(string name, Formula domain, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, domain)), Comma, Sp, body);
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Integer));

    private static Formula CountFormula()
    {
        var n = V("n");
        var f = V("f");
        var i = V("i");
        var k = V("k");
        var coefficient = App(Qualified("Polynomial", "coeff"), f, i);
        var binary = All("i", Natural,
            new Formula.Logic(EqTo(coefficient, D(0)), FormulaLogicOperator.Or,
                EqTo(coefficient, D(1))));
        var nullity = All("k", Integer,
            new Formula.Relation(Cast(D(3)), FormulaRelationOperator.Divides,
                App(Qualified("Polynomial", "eval"), k, f)));
        var predicate = And(EqTo(App(Qualified("Polynomial", "natDegree"), f), n),
            And(App(Qualified("Polynomial", "Monic"), f), And(binary, nullity)));
        var subtype = Seq(OpenBrace, f, Colon, Sp, Call("Polynomial", Integer),
            Sp, Slash, Slash, Sp, predicate, CloseBrace);
        return Disp(All("n", Natural,
            EqTo(Call("a", n), App(Qualified("Nat", "card"), subtype))));
    }

    private static Formula ClaimBody()
    {
        var n = V("n");
        Formula Term(byte offset) => Cast(Call("a", Subtract(n, D(offset))));
        Formula Multiple(byte coefficient, byte offset) => Multiply(D(coefficient), Term(offset));
        var rhs = Add(
            Subtract(
                Subtract(
                    Add(Subtract(Subtract(
                        Add(Multiple(2, 1), Multiple(2, 2)), Multiple(5, 3)), Multiple(2, 4)),
                        Multiply(D(1, 0), Term(5))), Multiple(4, 6)), Multiple(4, 7)),
            Multiple(8, 8));
        return All("n", Natural,
            new Formula.Logic(new Formula.Relation(D(9), FormulaRelationOperator.LessThanOrEqual, n),
                FormulaLogicOperator.Implies, EqTo(Cast(Call("a", n)), rhs)));
    }
}
