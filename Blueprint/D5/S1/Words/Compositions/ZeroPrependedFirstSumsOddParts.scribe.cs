using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class ZeroPrependedFirstSumsOddPartsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/oeis2026a392694");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero-prepended first sums of increasing positive lists correspond to odd-part partitions.",
        H("Zero-Prepended First Sums and Odd Parts"),
        Blocks(
            Paragraph(Text("OEIS A392694 concerns reversed partitions, meaning positive parts "
                + "in weakly increasing order. The zero-based alternating recurrence starts "
                + "at s0=0 and satisfies yj=s(j-1)+sj. The source condition is expressed by "
                + "an increasing positive preimage under the existing adjacent-sums definition. "
                + "The empty list is included. All counts below range over partitions of n.")),
            Node("IsZeroPrependedFirstSums", "The source predicate", PredicateFormula(),
                "There exists a weakly increasing positive list s whose adjacent sums after "
                + "prepending zero equal y. Fixed-start adjacent sums are injective. The "
                + "image is automatically positive and weakly increasing. No truncated "
                + "alternating subtraction is used in this definition.", DescribeRole.Definition),
            Node("card_zeroPrependedFirstSums_eq_odds", "The odd-parts correspondence", CountFormula("odds"),
                "Reverse s into the positive row lengths of a Young diagram, transpose, "
                + "and replace each column height h by 2h-1. This is an equivalence: odd "
                + "parts recover heights by (x+1)/2, and transposition is involutive. The "
                + "first-sums sum identity and the column identity prove preservation of "
                + "weight. Positive row lengths exclude zero padding. Sorting transports "
                + "the equivalence to Mathlib partitions of each n.", DescribeRole.Theorem),
            Node("card_zeroPrependedFirstSums_eq_distincts", "The A000009 count", CountFormula("distincts"),
                "Compose the new odd-parts counting theorem with Mathlib's "
                + "Nat.Partition.card_odds_eq_card_distincts. Thus the source count is "
                + "A000009(n), without a shift. At n=0 both sides count the single empty "
                + "partition. Euler's theorem is reused, not reproved.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a392694-zero-prepended-first-sums"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a392694-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Lists() => Call("List", Nat());
    private static Formula Qualifies(Formula y) => Call("IsZeroPrependedFirstSums", y);
    private static Formula Relation() => Par(Seq(V("a"), Comma, Sp, V("b"),
        Sp, Mapsto, Sp, V("a"), Sp, Le, Sp, V("b")));
    private static Formula PredicateFormula() => Disp(All(V("y"), Lists(), Seq(
        Qualifies(V("y")), Sp, Iff, Sp, Par(Seq(Exists, Sp, V("s"), Colon, Sp, Lists(),
            Comma, Sp, Call("Pairwise", Relation(), V("s")), Sp, Land, Sp,
            Par(All(V("x"), Nat(), Seq(V("x"), Sp, InMacro, Sp, V("s"), Sp, Implies, Sp,
                D(0), Sp, Lt, Sp, V("x")))), Sp, Land, Sp,
            Call("firstSums", Call("cons", D(0), V("s"))), Sp, Eq, Sp, V("y"))))));
    private static Formula CountFormula(string endpoint) => Disp(All(V("n"), Nat(), Seq(
        Call("card", Call("filter", Par(Seq(V("p"), Sp, Mapsto, Sp,
            Qualifies(Call("sort", Call("parts", V("p")), Relation())))),
            Par(Seq(Call("univ"), Colon, Sp, Call("Finset", Call("Partition", V("n"))))))),
        Sp, Eq, Sp, Call("card", Call(endpoint, V("n"))))));
}
