using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class ODorneyPadeJunctionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/odorney2026pade");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant in O'Dorney's Conjecture 4.7 vanishes at k=5, i=4, a=b=3.",
        H("O'Dorney's Padé junction determinant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("junction-determinant-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The universal determinant implication"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "On p. 16, O'Dorney writes, “The only solution to Υₖ,ᵢ(α) = 0 with "
                        + "a, b nonzero integers and D = a² + 4b > 0 occurs at k = 4, i = 3, "
                        + "a² = b, corresponding to the unique invisible junction in "
                        + "a⁴(Fₙ₊₁/Fₙ)⁴.”")),
                    Paragraph(Text(
                        "The discriminant is a²+4b with a and b cast from the integers to the reals. "
                        + "Set alpha=(a+sqrt(discriminant))/2 and h(X)=X²-aX-b. For 1≤i<k, "
                        + "beta at the integer index j is the coefficient of X^(2i-j) in "
                        + "h(X)^(i-1)(X-alpha)² when 0≤j≤2i, and zero otherwise. "
                        + "The entry in row r and column c of the (k-i) by (k-i) matrix "
                        + "is beta at the signed index i+c-r. The determinant is upsilon(a,b,k,i)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("junction-determinant-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The determinant vanishes outside the proposed exception"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take a=b=3, k=5 and i=4. The discriminant is 21 and the sole matrix "
                        + "entry is beta at index 4. By the one-by-one determinant identity, "
                        + "upsilon is the coefficient of X⁴ in (X²-3X-3)³(X-alpha)².")),
                    Paragraph(Text(
                        "The coefficients of X⁴, X³ and X² in (X²-3X-3)³ are 18, 27 and "
                        + "-54. Multiplication by (X-alpha)² therefore gives "
                        + "-54-54 alpha+18 alpha². Since alpha=(3+sqrt(21))/2 and "
                        + "sqrt(21)²=21, alpha²-3 alpha-3=0. Substitution gives zero for "
                        + "the coefficient of X⁴. The conclusion would force k=4, "
                        + "whereas this determinant has k=5.")),
                    Paragraph(Text(
                        "This resolves the determinant implication. The existence and "
                        + "classification of invisible junctions in actual continued-fraction "
                        + "decompositions are separate questions."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ClaimFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var k = F.Id("k");
        var i = F.Id("i");
        var discriminant = Seq(Operatorname, Grp(F.Id("discriminant")),
            Parenthesized(Seq(a, Comma, b)));
        var upsilon = Seq(Operatorname, Grp(F.Id("upsilon")),
            Parenthesized(Seq(a, Comma, b, Comma, k, Comma, i)));
        return Seq(
            Forall, Sp, Open, a, Comma, b, Colon, Mathbb, Grp(F.Id("Z")), Close, Sp,
            Open, k, Comma, i, Colon, Mathbb, Grp(F.Id("N")), Close, Comma, Sp,
            a, Neq, Sp, D(0), Sp, Longrightarrow, Sp,
            b, Neq, Sp, D(0), Sp, Longrightarrow, Sp,
            D(0), Lt, discriminant, Sp, Longrightarrow, Sp,
            D(1), Leq, Sp, i, Sp, Longrightarrow, Sp,
            i, Lt, k, Sp, Longrightarrow, Sp,
            upsilon, Eq, D(0), Sp, Longrightarrow, Sp,
            k, Eq, D(4), Sp, Land, Sp, i, Eq, D(3), Sp, Land, Sp,
            a, Caret, Grp(D(2)), Eq, b);
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
