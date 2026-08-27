using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Representation;

internal sealed class AlternatingFiveCharacterDecompositionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source-given A5 character rows verify the seven-dimensional decomposition class by class.",
        H("Seven-Dimensional A5 Character Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("alternating-five-character-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/Representation/"
                        + "AlternatingFiveCharacterDecomposition."
                        + "alternating_five_character_decomposition"),
                H("The seven-dimensional character is the sum of the 1, 3, and conjugate 3 rows"),
                StatementSource.FromAuthor(CharacterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite class type has exactly the labels 1A, 2A, 3A, 5A, and 5B. "
                            + "The four displayed rows are closed definitions of the values stated "
                            + "in the source: the target seven-dimensional character, the trivial "
                            + "character, and the two Galois-conjugate three-dimensional rows.")),
                    Paragraph(Text(
                        "Pointwise addition gives 1+3+3=7 on 1A, 1-1-1=-1 on 2A, "
                            + "and 1+0+0=1 on 3A. On 5A and 5B, the two golden values "
                            + "are exchanged, and Mathlib's goldenRatio_add_goldenConj identity "
                            + "reduces both sums to 2.")),
                    Paragraph(Text(
                        "This formalizes the atom's finite character-table verification. The A5 "
                            + "class labels and all character values are source-given data because "
                            + "neither this repository nor pinned Mathlib contains the concrete A5 "
                            + "character table. No representation objects are constructed here, so "
                            + "the result does not independently assert a Lean isomorphism of "
                            + "complex representations."))),
                DescribeRole.Theorem))));

    private static Formula Row(params Formula[] entries)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(entries[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula CharacterFormula()
    {
        Formula chi = F.Id("chi");
        Formula chiSeven = new Formula.Subscript(chi, D(7));
        Formula chiOne = new Formula.Subscript(chi, D(1));
        Formula chiThree = new Formula.Subscript(chi, D(3));
        Formula chiThreePrime =
            new Formula.Subscript(chi, Seq(D(3), Apos));
        Formula classes = Row(
            Seq(D(1), F.Id("A")), Seq(D(2), F.Id("A")),
            Seq(D(3), F.Id("A")), Seq(D(5), F.Id("A")),
            Seq(D(5), F.Id("B")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            F.Id("C"), Sp, Colon, Eq, Sp, classes, Comma, RowBreak, Grp(),
            chiSeven, Sp, Colon, Eq, Sp,
            Row(D(7), Seq(Minus, D(1)), D(1), D(2), D(2)),
            Comma, RowBreak, Grp(),
            chiOne, Sp, Colon, Eq, Sp,
            Row(D(1), D(1), D(1), D(1), D(1)), Comma, RowBreak, Grp(),
            chiThree, Sp, Colon, Eq, Sp,
            Row(D(3), Seq(Minus, D(1)), D(0), Varphi, Psi),
            Comma, RowBreak, Grp(),
            chiThreePrime, Sp, Colon, Eq, Sp,
            Row(D(3), Seq(Minus, D(1)), D(0), Psi, Varphi),
            Comma, RowBreak, Grp(),
            chiSeven, Sp, Eq, Sp, chiOne, Sp, Plus, Sp, chiThree,
            Sp, Plus, Sp, chiThreePrime, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
