using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class APIntersectionBoundaryEndgameDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary arithmetic-progression families admit recoverable endpoint codes.",
        H("Arithmetic Progressions and Boundary Codes"),
        Blocks(
            Node("is-ap-diff", "Arithmetic progression of fixed difference", "IsAPDiff",
                Disp(All(Iff(Call("IsAPDiff", F.Id("d"), F.Id("S")),
                    Ex("a", Nat(), Ex("n", Nat(), And(
                        Lt(D(0), F.Id("n")),
                        Eq(F.Id("S"), Call("apRange", F.Id("a"), F.Id("d"), F.Id("n"))))))),
                    ("d", Nat()), ("S", Finset(Nat())))),
                "A set is a finite arithmetic progression of difference d when it consists of a positive number of consecutive d-spaced terms starting at some natural number. The difference may be zero in this fixed-difference predicate.",
                DescribeRole.Definition),
            Node("is-ap", "Nonempty arithmetic progression", "IsAP",
                Disp(All(Iff(Call("IsAP", F.Id("S")),
                    Ex("d", Nat(), And(Lt(D(0), F.Id("d")), Call("IsAPDiff", F.Id("d"), F.Id("S"))))),
                    ("S", Finset(Nat())))),
                "A finite set is an arithmetic progression if it has a positive common difference and at least one term. Singletons and two-point sets qualify.",
                DescribeRole.Definition),
            Node("claim", "Boundary single-difference bound", "claim", null,
                "Let F be a family of subsets of [1,N], and let d be positive. Suppose intersections of distinct members are nonempty arithmetic progressions, every member of size at least four is an arithmetic progression, and every member avoiding 1 has at least four terms and difference d. Then F has at most C(N,2)+1 members.",
                DescribeRole.Definition),
            Node("terminal-triple-not-ap", "Terminal triple is not a progression", "terminal_triple_not_ap", null,
                "For positive d and k at least three, the set consisting of 1 and the two consecutive terminal points 1+(k-1)d and 1+kd is not an arithmetic progression.",
                DescribeRole.Lemma),
            Node("terminal-avoider-disjoint", "Terminal pair separates an avoider", "terminal_avoider_disjoint", null,
                "Let a progression from 1 have at least four terms, and let a second progression have positive length and positive difference. If its two external neighbours are the first progression's two terminal points and its left neighbour is at least 2, the progressions are disjoint.",
                DescribeRole.Lemma),
            Node("left-blocked-residue-recovery", "Recover a left-blocked residue", "left_blocked_residue_recovery", null,
                "For a positive common difference, two starts at least 2 whose left neighbours lie below 2 represent the same residue only when the starts agree. Equality of a point from each progression then also forces their indices to agree.",
                DescribeRole.Lemma),
            Node("right-blocked-length-recovery", "Recover a right-blocked length", "right_blocked_length_recovery", null,
                "At a fixed start and positive difference, two nonempty progressions whose final points do not exceed N and whose next points exceed N have the same length.",
                DescribeRole.Lemma),
            Node("avoider-no-neighbour-recovery", "Recover a progression without external neighbours", "avoider_no_neighbour_recovery", null,
                "Two nonempty progressions with the same positive difference, starts at least 2, and no external neighbour in [2,N] are equal if they intersect. Their shared point identifies the left-blocked residue, and the right boundary fixes the length.",
                DescribeRole.Lemma),
            Node("triple-terminal-separate", "Separate triples from terminal pairs", "triple_terminal_separate", null,
                "In a family whose distinct members intersect in nonempty arithmetic progressions, a member of size three containing 1 cannot share its two other points with the terminal pair of a member of at least four terms starting at 1. The resulting triple would be a non-progression contained in the longer member.",
                DescribeRole.Lemma),
            Node("none-code-separate", "Uniqueness of the extra code", "none_code_separate", null,
                "Under the boundary-family containment, intersection, and common-difference conditions, two distinct members cannot both receive the extra code. Members containing 1 would both be its singleton, while two members avoiding 1 would intersect as complete segments of the same residue class and hence coincide.",
                DescribeRole.Lemma),
            Node("point-code-separate", "Uniqueness of point codes", "point_code_separate", null,
                "Under the same containment, intersection, and avoider conditions, two distinct members cannot receive the same point code. A two-point member containing 1 is separated from an avoider by intersection, and an avoider's available neighbour determines its progression.",
                DescribeRole.Lemma)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Finset(Formula element) => Call("Finset", element);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
