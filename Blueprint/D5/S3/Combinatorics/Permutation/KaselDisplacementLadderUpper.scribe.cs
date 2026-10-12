using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class KaselDisplacementLadderUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized valid stage scheme attains displacement at most m minus two.",
        H("Kasel displacement upper construction"),
        Blocks(Describe.Lean(
            DescribeId.Create("upper-bound"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Permutation/KaselDisplacementLadderUpper.upper_bound"),
            H("An attaining normalized scheme"),
            StatementSource.FromAuthor(UpperBound()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every natural m at least two, there are stage and fibre-position functions "
                + "on the natural numbers giving a valid normalized scheme on S_A at horizon 4^m. "
                + "Every distinguished value has stage at most half its dyadic block index, "
                + "rounded down, plus m minus two. The distinguished set is "
                + "{3,4,9,10,11,12,13,14,15,16}.")),
                Paragraph(Text(
                    "Place 3 and 4 at stage one, and every other value at stage m. In the final "
                    + "fibre, all evens precede all odds. Within each parity, reverse the lowest "
                    + "2m+1 binary digits after XOR with target 4 for evens or target 3 for odds. "
                    + "This finite numeric rank decides comparisons at the lowest differing bit "
                    + "and puts its target first. It is injective below 2^(2m+1).")),
                Paragraph(Text(
                    "The endpoints of an arithmetic progression have equal parity. A different "
                    + "middle parity makes its position an extreme; equal parities reduce the "
                    + "same obstruction recursively by division by two. An early endpoint 4 is "
                    + "the least position, and an early endpoint 3 is least among odds. If an "
                    + "AP starts at 3 with an even middle value y greater than 4, the endpoint "
                    + "2y-3 has block index block(y)+1 and cannot belong to S_A. No considered AP "
                    + "has middle value 3 or 4. These facts exclude both increasing and decreasing "
                    + "APs in the stage concatenation.")),
                Paragraph(Text(
                    "Membership bounds the block index by 2m, giving normalization at stage m. "
                    + "The early values have block index two. The remaining distinguished "
                    + "values have block index four, so their displacement is exactly m minus two. "
                    + "This theorem establishes the upper construction; a matching lower bound "
                    + "is a separate assertion."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs"))]));

    private static Formula UpperBound()
    {
        var m = F.Id("m");
        var s = F.Id("s");
        var r = F.Id("r");
        var v = F.Id("v");
        var naturals = Seq(Mathbb, Sp, Grp(F.Id("N")));
        var domain = Call("SA", m);
        return Disp(Seq(Forall, Sp, m, Sp, InMacro, Sp, naturals, Comma, Sp,
            D(2), Sp, Le, Sp, m, Sp, Implies, Sp,
            Exists, Sp, s, Comma, Sp, r, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma, Sp,
            Call("Valid", domain, s, r), Sp, Land, Sp, Call("Normalized", domain, s), Sp, Land, Sp,
            Open, Forall, Sp, v, Sp, InMacro, Sp, F.Id("distinguished"), Comma, Sp,
            Call("s", v), Sp, Le, Sp,
            Lfloor, Sp, Call("block", v), Slash, D(2), Rfloor, Sp, Plus, Sp,
            Open, m, Sp, Minus, Sp, D(2), Close, Close));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
