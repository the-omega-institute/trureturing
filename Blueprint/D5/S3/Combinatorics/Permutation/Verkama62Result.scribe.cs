using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    private static Formula Name(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Name(s), [.. xs]);
    private static Formula All(string s, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Rel(Formula x, Formula token, Formula y) => Seq(x, Sp, token, Sp, y);
    private static Formula And(params Formula[] xs) => Seq([.. xs.SelectMany((x, i) =>
        i == 0 ? new Formula[] { Par(x) } : new Formula[] { Sp, Land, Sp, Par(x) })]);
    private static Formula Graph => Call("valueGraph", F.Id("p"));
    private static Formula Premises => And(Rel(D(3), Le, F.Id("n")),
        Seq(Neg, Sp, Call("ContainsOneBased", F.Id("p"))),
        Call("Connected", Graph),
        All("v", Call("Fin", F.Id("n")),
            Call("Connected", Call("delete", Graph, F.Id("v")))));
    private static Formula Bound => Rel(
        Seq(Frac, Grp(D(7)), Grp(D(4)), Sp, Cdot, Sp, F.Id("n"), Sp, Minus, Sp, D(3)),
        Le, Call("inv", Call("word", F.Id("p"))));
    private static Formula FinalStatement => All("n", Seq(Mathbb, Grp(F.Id("N"))),
        All("p", Call("Perm", Call("Fin", F.Id("n"))),
            new Formula.Logic(Par(Premises), FormulaLogicOperator.Implies, Par(Bound))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Verkama Conjecture 6.2.", H("Verkama Conjecture 6.2"), Blocks(
            Node("verkama62-result-complete-run", "Existence of a complete run", "complete_run",
                "For every n at least three and permutation pi of Fin n, assume the value-labelled inversion graph is connected and its induced complement of every singleton is connected. Then there is a northeast ear run ending at every point. An anchored triangle or 3412 square starts the construction. Induction on the number of missing points uses the anchored extension and the deletion connectivity of every run. This proof uses no pattern avoidance.", DescribeRole.Theorem),
            Node("verkama62-result-result", "The exact inversion bound", "result",
                "For every integer n at least zero and every permutation pi of {1,...,n}, suppose pi classically avoids 351624 and its inversion graph has at least three vertices, is connected, and remains connected after deletion of each vertex. Then inv(pi) is at least (7/4)n - 3, with comparison in the rationals. In the formula, delete(G,v) is the graph induced on all vertices other than v. In Lean the graph vertices are values in Fin n, the source label of i is i.val+1, and the graph is defined by the strictly negative integer product of the difference of value labels and the difference of their inverse-position labels. The at-least-three-vertices condition is 3 <= n. An occurrence uses six increasing positions and the relative value order [3,5,1,6,2,4], corresponding to [2,4,0,5,1,3] in Fin 6. The inversion statistic is the existing list counter on the one-based permutation word, proved equal to the number of increasing-position inversions, each counted once. A complete ear run and avoidance imply 7n <= 4 inv(pi)+12, which is equivalent to the displayed rational bound. No further avoidance, bipartiteness, asymptotic qualification, or assumed ear decomposition is used.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), declaration == "result" ? StatementSource.FromAuthor(Disp(FinalStatement)) : StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: declaration == "result"
                ? new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("verkama-2026-conjecture-62"), ResolutionKind.Proved)
                : null);
}
