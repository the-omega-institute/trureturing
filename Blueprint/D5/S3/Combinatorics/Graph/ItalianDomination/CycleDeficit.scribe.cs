using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ItalianDomination;

internal sealed class CycleDeficitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/shao2026italiandomination");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite binomial sum gives every Italian domination coefficient of a labelled simple cycle.",
        H("CycleDeficit"),
        Blocks(
            Node("binom", "binom", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("u"), Sp, F.Id("v"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, W("binom"), Sp, F.Id("u"), Sp, F.Id("v"), Sp, Eq, Sp, W("if"), Sp, D(0), Sp, Leq, Sp, F.Id("u"), Sp, Land, Sp, D(0), Sp, Leq, Sp, F.Id("v"), Sp, W("then"), Sp, Parenthesized(Seq(Q("Nat", "choose"), Sp, F.Id("u"), Sp, Dot, Sp, W("toNat"), Sp, F.Id("v"), Sp, Dot, Sp, W("toNat"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, W("else"), Sp, D(0))),
                "Ordinary binomial coefficients are extended by zero when either integer index is negative. For a nonnegative top an oversized bottom also has value zero.",
                "binom", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("zerofree", "zero Free", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, W("zeroFree"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, Eq, Sp, W("let"), Sp, F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Seq(Colon, Eq), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Semi, Sp, W("let"), Sp, F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Seq(Colon, Eq), Sp, D(2), Sp, Star, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Semi, Sp, W("if"), Sp, D(0), Sp, Leq, Sp, F.Id("r"), Sp, Land, Sp, D(2), Sp, Star, Sp, F.Id("r"), Sp, Leq, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Land, Sp, D(0), Sp, Lt, Sp, F.Id("s"), Sp, W("then"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Slash, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Star, Sp, W("binom"), Sp, F.Id("s"), Sp, F.Id("r"), Sp, W("else"), Sp, D(0))),
                "This term counts valid deficit words without a zero. The integer tests make the divisor positive before the rational division.",
                "zeroFree", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("allexceptional", "all Exceptional", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, W("allExceptional"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, Eq, Sp, W("if"), Sp, Q("Nat", "mod"), Sp, F.Id("n"), Sp, D(3), Sp, Eq, Sp, D(0), Sp, Land, Sp, D(3), Sp, Star, Sp, F.Id("j"), Sp, Eq, Sp, D(4), Sp, Star, Sp, F.Id("n"), Sp, W("then"), Sp, D(3), Sp, W("else"), Sp, D(0))),
                "This term records the three labelled shifts of a repetition of [0,2,2]. Nat.mod is natural-number remainder.",
                "allExceptional", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("gapterm", "gap Term", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("j"), Sp, F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, W("gapTerm"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, F.Id("a"), Sp, F.Id("b"), Sp, Eq, Sp, W("let"), Sp, F.Id("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Seq(Colon, Eq), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, D(2), Sp, Star, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, D(4), Sp, Star, Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Semi, Sp, W("let"), Sp, F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Seq(Colon, Eq), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Plus, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Plus, Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Semi, Sp, W("let"), Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Seq(Colon, Eq), Sp, F.Id("t"), Sp, Plus, Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Semi, Sp, W("if"), Sp, D(0), Sp, Leq, Sp, F.Id("c"), Sp, Land, Sp, D(1), Sp, Leq, Sp, F.Id("t"), Sp, W("then"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Slash, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Star, Sp, W("binom"), Sp, F.Id("m"), Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Star, Sp, W("binom"), Sp, Parenthesized(Seq(F.Id("c"), Sp, Plus, Sp, F.Id("t"), Sp, Minus, Sp, D(1))), Sp, F.Id("c"), Sp, Star, Sp, W("binom"), Sp, Parenthesized(Seq(F.Id("c"), Sp, Plus, Sp, F.Id("t"))), Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, W("else"), Sp, D(0))),
                "The integer parameters c, t and m give the number of ones, ordinary gaps and zeros. The tests require nonnegative c and positive t. Every displayed slash is rational division; its denominator is positive in the included case.",
                "gapTerm", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("closedform", "closed Form", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, W("closedForm"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, Eq, Sp, W("zeroFree"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, Plus, Sp, W("allExceptional"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, Plus, Sp, new Formula.Subscript(Sum, Seq(F.Id("b"), Sp, InMacro, Sp, Q("Finset", "range"), Sp, Parenthesized(Seq(F.Id("j"), Sp, Plus, Sp, D(1))))), Sp, new Formula.Subscript(Sum, Seq(F.Id("a"), Sp, InMacro, Sp, Q("Finset", "range"), Sp, Parenthesized(Seq(F.Id("j"), Sp, Plus, Sp, D(1))))), Sp, W("gapTerm"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, F.Id("a"), Sp, F.Id("b"))),
                "The two sums range over 0 through j. Outside the permissible gap parameters the summand is zero, so these finite ranges contain every contribution.",
                "closedForm", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "claim", Disp(Seq(W("claim"), Sp, Eq, Sp, Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(3), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, F.Id("j"), Sp, Leq, Sp, D(2), Sp, Star, Sp, F.Id("n"), Sp, To, Sp, Parenthesized(Seq(W("dI"), Sp, F.Id("n"), Sp, Parenthesized(Seq(D(2), Sp, Star, Sp, F.Id("n"), Sp, Minus, Sp, F.Id("j"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Eq, Sp, W("closedForm"), Sp, F.Id("n"), Sp, F.Id("j"))),
                "The assertion gives the finite coefficient sum for every n ≥ 3 and 0 ≤ j ≤ 2n, answering the fourth question of Shao and Zhao, §9 (p. 29). The carrier Fin n fixes the vertex labels; no rotation or reflection quotient is taken. The value at weight zero is the same subtype count.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "result", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(3), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, F.Id("j"), Sp, Leq, Sp, D(2), Sp, Star, Sp, F.Id("n"), Sp, To, Sp, Parenthesized(Seq(W("dI"), Sp, F.Id("n"), Sp, Parenthesized(Seq(D(2), Sp, Star, Sp, F.Id("n"), Sp, Minus, Sp, F.Id("j"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Eq, Sp, W("closedForm"), Sp, F.Id("n"), Sp, F.Id("j"))),
                "Complement each label f(i) to 2−f(i). A pair of consecutive twos must be flanked by zeros; every zero-free gap is either exactly [2,2] or has no adjacent twos. Marking a zero gives ordered gaps, and removing the mark multiplies the count by the number of zeros, even for periodic words. Weak compositions distribute the ones; subsets of insertion slots place the isolated twos. The all-exceptional case contributes three labelled shifts. Marking a one counts the class without zeros. The disjoint classes yield the displayed identity.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("shao-zhao-italian-cycle-closed-form"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("cycle-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula W(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(W(owner), Dot, W(name));
}
