using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class CrimFourPartClassificationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Games/CrimFourPartClassification";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Certificates/basic2026crim");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An unbounded classification of all losing four-part positions in normal-play CRIM.",
        H("Losing four-part CRIM positions"),
        Blocks(
            Node("claim", "The four-part classification", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                "Section 5, Question 1, p. 17: “Which partitions consisting of four parts are losing?” "
                + "The natural numbers a, b, c, d are the positive row lengths, ordered from largest to smallest. "
                + "The function grundy is the original CRIM evaluator: a move deletes a row, or conjugates, "
                + "deletes a row and conjugates back. Losing means Grundy value zero. "
                + "The displayed equivalence answers the question on its entire four-part domain. "
                + "Nat.mod is natural-number remainder; each remainder has divisor two. The four alternatives may overlap.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("result", "Exactly the losing four-part positions", ClaimBody(),
                "The four alternatives, together with even a, are necessary and sufficient. "
                + "The proof treats every sorted nonnegative quadruple after removing zero entries. "
                + "Each legal column deletion subtracts one from the first one, two, three or four entries, "
                + "with a strict gap at the cut. Together with the four row deletions these exhaust the moves. "
                + "A losing candidate has no losing candidate as a follower; every other position has one. "
                + "Strong induction on the number of cells, using the CRIM mex recursion and strict descent, "
                + "therefore identifies the candidate predicate with Grundy value zero. "
                + "For three positive parts the auxiliary predicate excludes the column [1,1,1]. "
                + "There is no upper bound on a, b, c or d. The theorem determines zero versus nonzero, "
                + "and does not determine the positive Grundy values or classify all positions with five rows.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("crim-question-one-four-parts"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("crim-four-" + name), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Rem(Formula n) => App(Qualified("Nat", "mod"), n, D(2));

    private static Formula ClaimBody()
    {
        var a = F.Id("a"); var b = F.Id("b"); var c = F.Id("c"); var d = F.Id("d");
        var partA = And(Leq(D(2), d), Seq(Neg, Parenthesized(And(Equal(Rem(b), D(1)), Equal(Rem(c), D(1))))));
        var partB = And(Equal(d, D(1)), And(Equal(c, D(1)), Or(Equal(Rem(b), D(0)), Equal(b, D(1)))));
        var partC = And(Equal(d, D(1)), And(Leq(D(2), c), Equal(Rem(b), D(1))));
        var partD = And(Equal(d, D(1)), And(Equal(c, D(2)), Or(Leq(D(3), b), Equal(a, D(2)))));
        var rows = Seq(OpenBracket, a, Comma, b, Comma, c, Comma, d, CloseBracket);
        var losing = Equal(Call("grundy", rows), D(0));
        var classified = And(Equal(Rem(a), D(0)), Or(partA, Or(partB, Or(partC, partD))));
        return All("a", Nat, All("b", Nat, All("c", Nat, All("d", Nat,
            Imp(Leq(D(1), d), Imp(Leq(d, c), Imp(Leq(c, b), Imp(Leq(b, a),
                Logic(losing, FormulaLogicOperator.Iff, classified)))))))));
    }
}
