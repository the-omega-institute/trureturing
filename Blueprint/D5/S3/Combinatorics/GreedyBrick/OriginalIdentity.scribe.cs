using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GreedyBrick;

internal sealed class OriginalIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GreedyBrick/OriginalIdentity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/udovenko2026a395531");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first brick widths in every positive row satisfy the greedy-brick composition identity.",
        H("The Greedy-Brick All-Index Identity"),
        Blocks(
            Paragraph(Text("Bricks have widths 1,2,3,... and unit height. Each brick occupies "
                + "the highest fully supported row as close to the vertical axis as possible. "
                + "Rows are numbered from one. The deterministic capacity trajectory is "
                + "conjugate to the literal row scan and has one common labelled rectangle history. "
                + "Every positive row has a least birth. The width of its first brick equals "
                + "that birth's brick index.")),
            Describe.Lean(DescribeId.Create("greedy-brick-original-sequence"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal first-birth sequence"),
                StatementSource.FromAuthor(Disp(Equal(A(M()), Seq(
                    Named("if"), Sp, D(1), Sp, Le, Sp, M(), Sp,
                    Named("then"), Sp, Call("birth", M()), Sp,
                    Named("else"), Sp, D(0))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive m, birth(m) is the least brick index "
                    + "at which the actual trajectory has m rows. Its existence is proved "
                    + "for every m. The value at zero is unused."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("greedy-brick-original-all-index-identity"),
                DeclarationHandle.Create(Prefix + "result"), H("Udovenko's all-index identity"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, M(), Colon, Sp,
                    Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
                    D(1), Sp, Le, Sp, M(), Sp, Implies, Sp,
                    Equal(A(A(M())), Subtract(
                        new Formula.Floor(new Formula.Fraction(Mul(A(M()), Add(A(M()), D(3))), D(2))), M()))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("At a rest endpoint, the least zero capacity chooses the "
                        + "length of the next block. An induction through the positive capacity "
                        + "prefix shows that no row is born strictly before that block ends. "
                        + "The cofinal rest clock therefore identifies every literal least "
                        + "row birth with its event-birth endpoint.")),
                    Paragraph(Text("Write b(m) for this common birth width. The successor band "
                        + "places a renewal before birth b(m) exactly when its immediate "
                        + "predecessor is before birth m. Successor and predecessor are inverse "
                        + "on these two cuts and preserve bin labels. Endpoint increments "
                        + "telescope to their weights. Births through b(m) contribute "
                        + "b(m)(b(m)+1)/2 and renewals contribute b(m)-m. Adding these "
                        + "weights gives the stated identity. This argument does not require "
                        + "the chronological renewal labels to copy an earlier word."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a395531-greedy-brick-all-index"),
                    ResolutionKind.Proved)))));

    private static Formula M() => F.Id("m");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula A(Formula index) => Call("a", index);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
