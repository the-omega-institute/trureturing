using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedTailComparisonDocument : IScribeDocumentDefinition
{
    private static Formula X => F.Id("x");
    private static Formula N => F.Id("N");
    private static Formula T => F.Id("t");
    private static Formula A => F.Id("A");
    private static Formula B => F.Id("B");
    private static Formula Profile => Call("f", X);
    private static Formula Square => Seq(Profile, Caret, Grp(D(2)));
    private static Formula AbsX => Seq(Left, Lvert, Sp, X, Right, Rvert);
    private static Formula AllX => Seq(Forall, Sp, X, Comma, Sp);

    private static Formula Statement => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Open, AllX, AbsX, Gt, N, Sp, Longrightarrow, Sp, Open,
        A, Cdot, Sp, Square, Le, Sp, Call("G", X), Sp, Land, Sp,
        Call("L", X), Le, Sp, B, Cdot, Sp, Square, Close, Close,
        RowBreak, Grp(), Quad, Longrightarrow, Sp,
        Exists, Sp, T, Gt, D(0), Comma, Sp, AllX,
        T, Cdot, Sp, Profile, Le, Sp, Call("rawOccupation", X),
        End, Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual positive forcing supplies the finite-core part of a globally scaled subsolution.",
        H("Actual occupation comparison from compensated tail estimates"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-lower-from-tail-estimates"),
            DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedTailComparison.actual_lower_from_tail_estimates"),
            H("From eventual quadratic gain and loss to a global lower bound"),
            StatementSource.FromAuthor(Statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let f be a nonnegative real profile on the integers bounded by F>0, with summable squares. Fix A>0, B>=0 and a natural cutoff N. Here G(x) is the actual kernel-weight series of f(x+i+1)+f(x-i-1)-2 f(x); L(x) is the actual loss-weight series of f(x+i+1)^2+f(x-i-1)^2, both for i>=0. The first line assumes the gain and loss estimates for every integer outside the stated core.")),
                Paragraph(Text("The finite core includes both endpoints. Its actual positive forcing has a positive minimum: away from zero, the count of shapes is positive because it includes the identity avoider. The scale is chosen so that the scaled values fit the actual mass box, every neighbor term is nonnegative on the core, and the scaled profile is smaller than the core forcing.")),
                Paragraph(Text("Outside the core, the actual kernel mass of one half converts the compensated series back to the paired linear sum minus f(x). The positive scale makes its linear gain dominate the actual rational loss, which is bounded by the squared scale divided by the positive denominator constant h. Square-summability supplies the required finite positive level sets for the existing comparison theorem. This does not claim that any particular nonzero profile meets the tail assumptions."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
