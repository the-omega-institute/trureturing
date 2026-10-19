using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

public sealed class FiniteOttoCongruence : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/FiniteOttoCongruence.";
    private static LibraryNoteRef Jack => LibraryNoteRef.Create("D5/L/FiniteGroups/jack2026conjugacy");
    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp);
    private static Formula Instance(string name) =>
        Seq(OpenBracket, Call(name, V("S")), CloseBracket, Sp);
    private static Formula Context => Seq(All("S", Seq(V("Type"), Star)), Instance("Semigroup"));
    private static Formula Otto(Formula a, Formula b) => Call("Otto", a, b);
    private static Formula Product(Formula a, Formula b) => Multiply(a, b);
    private static Formula CancellationBody => Seq(
        Parenthesized(Seq(All("a", V("S")), All("b", V("S")), All("c", V("S")),
            Otto(Product(V("a"), V("b")), Product(V("a"), V("c"))), Sp, Rightarrow, Sp,
            Otto(V("b"), V("c")))), Sp, Land, Sp,
        Parenthesized(Seq(All("a", V("S")), All("b", V("S")), All("c", V("S")),
            Otto(Product(V("b"), V("a")), Product(V("c"), V("a"))), Sp, Rightarrow, Sp,
            Otto(V("b"), V("c")))));
    private static Formula ClaimBody() => Seq(All("S", V("Type")), Instance("Semigroup"),
        Instance("Finite"), Call("OttoIsCongruence", V("S")), Sp, Rightarrow, Sp,
        Call("QuotientCancelative", V("S")));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite semigroups with an Otto congruence have cancellative quotients.",
        H("Finite Otto congruence quotients are cancellative"), Blocks(
            Node("otto", "Otto", "Otto conjugacy", Seq(Context,
                All("a", V("S")), All("b", V("S")), Otto(V("a"), V("b")), Sp, Iff, Sp,
                Exists, Sp, V("g"), Comma, Sp, V("h"), Colon, Sp, V("S"), Comma, Sp,
                Equal(Product(V("a"), V("g")), Product(V("g"), V("b"))), Sp, Land, Sp,
                Equal(Product(V("b"), V("h")), Product(V("h"), V("a")))),
                "Jack, Section 2, p. 2: \"∀a, b ∈ S (a ∼o b ⇔ ag = gb and bh = ha for some g, h ∈ S).\" "
                    + "Otto(a,b) uses two witnesses from S itself; no identity element is adjoined. "
                    + "S is an arbitrary semigroup, with no nonemptiness assumption.",
                AssessedProvenance.FromLiterature(Jack), DescribeRole.Definition),
            Node("congruence", "OttoIsCongruence", "Compatibility with multiplication", Seq(Context,
                Call("OttoIsCongruence", V("S")), Sp, Iff, Sp,
                Parenthesized(Seq(All("a", V("S")), All("b", V("S")), All("c", V("S")), All("d", V("S")),
                    Otto(V("a"), V("b")), Sp, Rightarrow, Sp, Otto(V("c"), V("d")), Sp, Rightarrow, Sp,
                    Otto(Product(V("a"), V("c")), Product(V("b"), V("d")))))),
                "Otto conjugacy is an equivalence relation for every semigroup. "
                    + "Its being a congruence means that multiplication respects two pairs of related elements. "
                    + "This is the congruence condition in Jack's Section 9, Problem 9.4, p. 14.",
                AssessedProvenance.FromLiterature(Jack), DescribeRole.Definition),
            Node("cancellation", "QuotientCancelative", "Cancellation of classes", Seq(Context,
                Call("QuotientCancelative", V("S")), Sp, Iff, Sp, Parenthesized(CancellationBody)),
                "The first conjunct is left cancellation and the second is right cancellation, expressed on representatives. "
                    + "When Otto conjugacy is a congruence, these are exactly the two cancellation laws of the quotient semigroup. "
                    + "The spelling cancelative follows Jack's Section 9, Problem 9.4, p. 14.",
                AssessedProvenance.FromLiterature(Jack), DescribeRole.Definition),
            Node("claim", "claim", "The negative answer to Problem 9.4", Seq(V("claim"), Sp, Iff, Sp,
                Parenthesized(ClaimBody())),
                "Jack, Section 9, Problem 9.4, p. 14: \"Is there a finite semigroup for which ∼o is a congruence and S/∼o is not cancelative?\" "
                    + "The proposition gives the negative answer: for every finite semigroup S, multiplication compatibility "
                    + "of Otto conjugacy implies both cancellation laws on classes. Type denotes the small carrier universe; "
                    + "Finite imposes no chosen enumeration. Empty carriers satisfy the statement vacuously.",
                AssessedProvenance.FromLiterature(Jack), DescribeRole.Definition),
            Node("result", "result", "Every finite Otto congruence quotient is cancellative", ClaimBody(),
                "Every element of a finite semigroup has an idempotent positive power. "
                    + "All idempotents are Otto-conjugate, using the products ef and fe as witnesses. "
                    + "If an idempotent power of a is a to the n, then a is Otto-conjugate to a to the n plus one. "
                    + "Multiplication compatibility therefore makes the common idempotent class a two-sided identity. "
                    + "The preceding positive power supplies an inverse class, proving left cancellation. "
                    + "The relation between ab and ba, witnessed by a and b, transfers this to right cancellation.",
                AssessedProvenance.FromRepo(Jack), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jack-2024-finite-otto-congruence"),
                    ResolutionKind.Proved)))));
}
