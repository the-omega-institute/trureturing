using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.FiniteGeometry.RectangleIdentifiability;

internal sealed class ThreeRowBlackoutMaximumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum";
    private static LibraryNoteRef SourceNote => LibraryNoteRef.Create("D5/L/pemmasani2026blackouts");
    private static LibraryNoteRef GeometryNote => LibraryNoteRef.Create("D5/L/partridge2017a289832");
    private static Formula M => F.Id("m");
    private static Formula C => F.Id("C");
    private static Formula S => F.Id("S");
    private static Formula T => F.Id("D");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula P => F.Id("c");
    private static Formula Q => F.Id("d");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Paren(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Call(string name, Formula value) => Seq(Named(name), Paren(value));
    private static Formula Grid => Seq(Call("Fin", M), Times, Call("Fin", D(3)));
    private static Formula Sets => Seq(Named("Finset"), Paren(Grid));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, type, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Colon, type, Comma, Sp, body);
    private static Formula X(Formula point) => Call("x", point);
    private static Formula Y(Formula point) => Call("y", point);
    private static Formula Difference(Formula first, Formula second) => Paren(Seq(first, Minus, second));
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Rectangle(Formula value) => Call("IsRectangle", value);
    private static Formula Valid(Formula value) => Call("ValidBlackout", value);
    private static Formula Orthogonal => Seq(
        Difference(X(B), X(A)), Cdot, Difference(X(P), X(A)), Plus,
        Difference(Y(B), Y(A)), Cdot, Difference(Y(P), Y(A)), Eq, D(0));
    private static Formula RectangleDefinition => All(M, Naturals, All(C, Sets,
        Seq(Rectangle(C), Iff, Paren(Seq(Card(C), Eq, D(4), Land,
            Some(Seq(A, Sp, B, Sp, P, Sp, Q), Grid, Seq(
                C, Eq, OpenBrace, A, Comma, B, Comma, P, Comma, Q, CloseBrace, Land,
                Orthogonal, Land, X(A), Plus, X(Q), Eq, X(B), Plus, X(P), Land,
                Y(A), Plus, Y(Q), Eq, Y(B), Plus, Y(P))))))));
    private static Formula ValidDefinition => All(M, Naturals, All(S, Sets,
        Seq(Valid(S), Iff, Paren(All(Seq(C, Sp, T), Sets, Seq(
            Rectangle(C), Implies, Sp, Rectangle(T), Implies, Sp,
            C, Setminus, Sp, S, Eq, T, Setminus, Sp, S, Implies, Sp, C, Eq, T))))));
    private static Formula FullResult => All(M, Naturals, Seq(D(3), Leq, Sp, M, Implies, Sp,
        Paren(Some(S, Sets, Seq(Valid(S), Land, Card(S), Eq, M, Plus, D(2)))), Land,
        Paren(All(S, Sets, Seq(Valid(S), Implies, Sp, Card(S), Leq, Sp, M, Plus, D(2))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-row lattice grid of every width at least three admits exactly the conjectured maximum number of blacked-out points.",
        H("The Three-Row Blackout Maximum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rectangle-corner-sets"),
                DeclarationHandle.Create(Module + ".IsRectangle"),
                H("The full rectangle family"),
                StatementSource.FromAuthor(Disp(RectangleDefinition)),
                AssessedProvenance.FromLiterature(SourceNote),
                Blocks(Paragraph(Text(
                    "The first coordinate is column and the second row. In this formula x and y "
                    + "are the respective coordinate values cast to integers. Four distinct corners, "
                    + "perpendicular adjacent vectors and the parallelogram equations describe "
                    + "every nondegenerate Euclidean rectangle on the grid, including squares "
                    + "and tilted rectangles. Corner sets are unordered."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("valid-blackouts"),
                DeclarationHandle.Create(Module + ".ValidBlackout"),
                H("Identifiability after deletion"),
                StatementSource.FromAuthor(Disp(ValidDefinition)),
                AssessedProvenance.FromLiterature(SourceNote),
                Blocks(Paragraph(Text(
                    "A blackout is chosen before the rectangle. Its presentation is the corner "
                    + "set after deleting blacked-out points. Validity requires that equal "
                    + "presentations imply equal corner sets. Empty presentations are allowed; "
                    + "injectivity itself ensures that at most one rectangle is entirely hidden."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-row-maximum"),
                DeclarationHandle.Create(Module + ".result"),
                H("Pemmasani's exact maximum"),
                StatementSource.FromAuthor(Disp(FullResult)),
                AssessedProvenance.FromRepo(SourceNote, GeometryNote),
                Blocks(
                    Paragraph(Text(
                        "For every natural width at least three, the theorem constructs a valid "
                        + "blackout with width plus two points and proves that every valid blackout "
                        + "has at most that size. Both clauses refer to the full rectangle family.")),
                    Paragraph(Text(
                        "The attaining set is the union of a boundary row and a boundary column. "
                        + "The proof establishes the known classification from Partridge's A289832: "
                        + "all three-row rectangles are axis rectangles or unit diamonds on three "
                        + "consecutive columns. Their visible corners distinguish "
                        + "all pairs after this deletion.")),
                    Paragraph(Text(
                        "For the upper bound, two different columns cannot both hide the same "
                        + "pair of rows: comparison with a third column would give colliding "
                        + "rectangle presentations. This is Pemmasani's two-row Strip Theorem "
                        + "obstruction, proved locally. A second collision rules out independent "
                        + "overlaps of all three row pairs. Finite-set inclusion-exclusion then "
                        + "bounds the total by the width plus two. No source numerical table or "
                        + "diagram is used as a premise."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397315-three-row-blackout"),
                    ResolutionKind.Proved)))));
}
