using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class MatchedResidualOccupationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/MatchedResidualOccupation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pointwise matching controls a subset of the weighted occupation pairs.",
        H("Weight of matched occupations"),
        Blocks(Describe.Lean(
            DescribeId.Create("matched-occupation-mass-le"),
            DeclarationHandle.Create(Owner + ".matched_occupation_mass_le"),
            H("Multinomial mass under a pointwise matching"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be finite with nonnegative real weights w. Let E be a relation on J. "
                    + "The sum of w(i)w(j) over ordered edges of E is denoted by R. "
                    + "Let S be a set of ordered pairs of degree-d count vectors. Each pair "
                    + "in S has representative words whose corresponding letters lie in E. "
                    + "The function c with subscript d denotes the weighted multinomial coefficient.")),
                Paragraph(Text(
                    "For either count vector, all representative words differ only by a "
                    + "permutation. Thus every pair of representative words admits some matching. "
                    + "Their weights sum to the product of the two multinomial coefficients.")),
                Paragraph(Text(
                    "Sum over all position permutations. Each matchable word pair contributes "
                    + "its nonnegative weight at least once. For a fixed permutation, the two words "
                    + "are equivalent to a length-d word of ordered pairs of letters. Each position "
                    + "contributes the same edge mass R. There are d factorial permutations."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var d = F.Id("d");
        var a = F.Id("a");
        var b = F.Id("b");
        var coefficient = new Formula.Subscript(F.Id("c"), d);
        var pairs = Seq(Open, a, Comma, b, Close, Sp, InMacro, Sp, F.Id("S"));
        return Disp(Seq(
            new Formula.Subscript(Sum, pairs), Sp,
            coefficient, Open, a, Close, Sp, coefficient, Open, b, Close, Sp, Leq, Sp,
            d, Bang, Sp, new Formula.Power(F.Id("R"), d)));
    }
}
