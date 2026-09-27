using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphIrregularity;

internal sealed class LinkIrregularTournamentExistenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/bastienkhormali2025digraphs");
    private static readonly LibraryNoteRef ClassicalFamily =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/schmerltrotter1993critical");
    private static readonly LibraryNoteRef DeletionMethod =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/belkhechineboudabbous2010indecomposable");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Link-irregular tournaments exist at every nonvacuous order exactly from six onward.",
        H("Existence of Link-Irregular Tournaments"),
        Blocks(
            Paragraph(Text(
                "Bastien and Khormali define directed links using the union of the out- and "
                    + "in-neighbors and state the all-orders existence assertion as Conjecture 6. "
                    + "The pairwise condition is vacuous on zero and one vertices, so the exact "
                    + "threshold theorem is stated on the nonvacuous domain n at least two.")),
            Describe.Lean(
                DescribeId.Create("tournament"),
                DeclarationHandle.Create(Prefix + "IsTournament"),
                H("Tournament orientation"),
                StatementSource.FromAuthor(IsTournamentFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A tournament relation is irreflexive. For every two distinct vertices, "
                        + "exactly one of the two possible directed edges is present. The exclusive "
                        + "disjunction retains both existence and uniqueness of the orientation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("directed-link"),
                DeclarationHandle.Create(Prefix + "DirectedLink"),
                H("Directed link"),
                StatementSource.FromAuthor(DirectedLinkFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The carrier contains exactly the vertices w for which v points to w or w "
                        + "points to v. Subrel restricts the original directed relation to that "
                        + "carrier, so the link is the induced directed relation rather than an "
                        + "invariant or numerical summary."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("link-irregular"),
                DeclarationHandle.Create(Prefix + "LinkIrregular"),
                H("Pairwise link irregularity"),
                StatementSource.FromAuthor(LinkIrregularFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each ordered pair of distinct vertices, the type of relation "
                        + "isomorphisms between their actual directed links is empty. RelIso is "
                        + "Mathlib's arbitrary bijective relation isomorphism; no selected "
                        + "invariant or restricted family of permutations replaces it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("link-irregular-tournament-existence"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The exact nonvacuous threshold"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source, ClassicalFamily, DeletionMethod),
                Blocks(
                    Paragraph(Text(
                        "For orders two through five, every tournament has two deletion cards "
                            + "that are isomorphic as directed relations. The proof uses the exact "
                            + "one, one, two, and four isomorphism-class bounds for card orders one "
                            + "through four, together with pigeonhole.")),
                    Paragraph(Text(
                        "At order six, the proof checks the fifteen arcs displayed in the source "
                            + "and excludes every relation isomorphism between every pair of cards "
                            + "inside the kernel. This finite calculation is confined to the proof "
                            + "and does not replace the quantified theorem.")),
                    Paragraph(Text(
                        "For every order at least seven, take a transitive chain and an additional "
                            + "pivot pointing to the even zero-based chain labels and receiving "
                            + "arcs from the odd labels. At odd orders this is the classical W family "
                            + "of Schmerl--Trotter, also recalled by Belkhechine and Boudabbous; "
                            + "at even orders it is the preceding odd-order W with one added sink. "
                            + "After deleting any one chain vertex, further deletion of the pivot "
                            + "leaves a transitive tournament, while further deletion of any other "
                            + "vertex leaves an intact triangle among the pivot and one of three "
                            + "disjoint adjacent chain pairs. Thus the pivot is uniquely determined "
                            + "within each chain-deleted card, so any isomorphism between two such "
                            + "cards fixes it. Rigidity of the remaining finite chain then fixes "
                            + "every rank, and the smaller deleted rank has opposite parity on the "
                            + "two cards, contradicting preservation of the pivot edge. Deleting "
                            + "the pivot itself gives a transitive card; chain-deleted cards are not "
                            + "transitive.")),
                    Paragraph(Text(
                        "The conclusion quantifies over all natural n satisfying 2 <= n and over "
                            + "all tournament relations on Fin(n). It proves both existence from "
                            + "six onward and nonexistence below six; orders zero and one are "
                            + "outside the statement because their pairwise condition is vacuous."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bastien-khormali-link-irregular-tournaments"),
                    ResolutionKind.Proved)))));

    private static Formula IsTournamentFormula()
    {
        Formula vertex = F.Id("V"), relation = F.Id("R");
        Formula v = F.Id("v"), u = F.Id("u");
        Formula loopless = All("v", vertex,
            new Formula.Not(At(relation, v, v)));
        Formula oriented = All("u", vertex, All("v", vertex,
            Implies(NotEqual(u, v),
                Call("Xor", At(relation, u, v), At(relation, v, u)))));
        return Disp(All("V", Type(), All("R", Relation(vertex),
            Iff(Call("IsTournament", relation), And(loopless, oriented)))));
    }

    private static Formula DirectedLinkFormula()
    {
        Formula vertex = F.Id("V"), relation = F.Id("R");
        Formula v = F.Id("v"), w = F.Id("w");
        Formula neighbors = Lambda(w, vertex,
            Or(At(relation, v, w), At(relation, w, v)));
        return Disp(All("V", Type(), All("R", Relation(vertex), All("v", vertex,
            Equal(Call("DirectedLink", relation, v),
                Call("Subrel", relation, neighbors))))));
    }

    private static Formula LinkIrregularFormula()
    {
        Formula vertex = F.Id("V"), relation = F.Id("R");
        Formula u = F.Id("u"), v = F.Id("v");
        Formula isomorphisms = Call("RelIso",
            Call("DirectedLink", relation, u), Call("DirectedLink", relation, v));
        Formula pairwise = All("u", vertex, All("v", vertex,
            Implies(NotEqual(u, v), Call("IsEmpty", isomorphisms))));
        return Disp(All("V", Type(), All("R", Relation(vertex),
            Iff(Call("LinkIrregular", relation), pairwise))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), relation = F.Id("R");
        Formula fin = Call("Fin", n);
        Formula witness = ExistsOne("R", Relation(fin),
            And(Call("IsTournament", relation), Call("LinkIrregular", relation)));
        return Disp(All("n", Naturals(),
            Implies(LessEqual(D(2), n), Iff(witness, LessEqual(D(6), n)))));
    }

    private static Formula Type() => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula Prop() => Seq(Operatorname, Grp(F.Id("Prop")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Relation(Formula vertex) =>
        new Formula.TypeArrow(vertex, new Formula.TypeArrow(vertex, Prop()));

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Parenthesized(Seq(variable, Colon, Sp, domain, Sp, Mapsto, Sp, body));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And,
            Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or,
            Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula ExistsOne(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
}
