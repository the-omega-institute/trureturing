using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.Asymptotics;

internal sealed class ExactDecksAsymptoticsPositivePairExactDeckAsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ExactDecks/Asymptotics/PositivePairExactDeckAsymptotics";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact k-deck images have the full weighted-Lyndon asymptotic exponent.",
        H("PositivePairExactDeckAsymptotics"),
        Blocks(
            Paragraph(Text(
                "The lower estimate comes from actual equal-length positive-word constructions. "
                + "For the upper estimate, one singleton Lyndon coordinate is erased and recovered "
                + "from the fixed total source length; unconditional Lyndon-coordinate recovery "
                + "then identifies the complete exact deck. Thus exactly one degree of freedom is "
                + "removed, without an additional hypothesis on n or k.")),
            D("actual-exact-deck-weighted-lyndon-theta", "actual_exactKDeckImage_weightedLyndon_isTheta", "Full exact k-deck Conjecture 8.1 asymptotics",
                "For every finite linearly ordered type A with 2<=Fintype.card A, every k:N with 1<=k, the real-valued function n |-> (exactKDeckImage A k n).card is Real.IsTheta at Filter.atTop of n |-> (n:R)^(weightedLyndonExponent A k-1). Here weightedLyndonExponent is the weighted sum of the actual length-r Lyndon-word counts, so the theorem has all source quantifiers and no proxy parameter."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Seq(Forall, Sp,
                F.Id("A"), Comma, Sp, F.Id("k"), Comma, Sp,
                Call("FiniteLinearOrder", F.Id("A")), Comma, Sp,
                Call("card", F.Id("A")), Sp, Geq, Sp, F.D(2), Comma, Sp,
                F.Id("k"), Sp, Geq, Sp, F.D(1), Sp, Rightarrow, Sp,
                Call("RealIsTheta", F.Id("atTop"),
                    Call("lambda", F.Id("n"), Call("castR", Call("card",
                        Call("exactKDeckImage", F.Id("A"), F.Id("k"), F.Id("n"))))),
                    Call("lambda", F.Id("n"), Call("pow", Call("castR", F.Id("n")),
                        Subtract(Call("weightedLyndonExponent", F.Id("A"), F.Id("k")),
                            Num(1)))))))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
