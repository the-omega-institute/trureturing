using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class ReciprocityParityErrorDetectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A valid finite sign report detects one flipped symbol but can accept two flips.",
        H("Reciprocity Parity Error Detection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reciprocity-parity-error-detection"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/ReciprocityParityErrorDetection."
                        + "reciprocity_parity_error_detection"),
                H("A parity report detects one flip but not every pair of flips"),
                StatementSource.FromAuthor(ErrorDetectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite report of integer signs whose product is one, flipping "
                            + "either of two selected coordinates changes the product to minus "
                            + "one. The two single-error syndromes are equal, so this one check "
                            + "does not identify which selected coordinate was flipped.")),
                    Paragraph(Text(
                        "If the two selected coordinates are distinct, flipping both restores "
                            + "the product to one. This supplies an explicit even-error pattern "
                            + "that the parity check accepts."))),
                DescribeRole.Theorem))));

    private static Formula ErrorDetectionFormula()
    {
        Formula carrier = F.Id("I");
        Formula places = F.Id("S");
        Formula profile = F.Id("profile");
        Formula first = F.Id("a");
        Formula second = F.Id("b");
        Formula place = F.Id("v");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula signs = Seq(Operatorname, Grp(F.Id("ZUnits")));
        Formula firstFlip = SignProduct(places, place,
            Call("flipLocalSign", profile, first, place));
        Formula secondFlip = SignProduct(places, place,
            Call("flipLocalSign", profile, second, place));
        Formula doubleFlip = SignProduct(places, place,
            Call("update", Call("flipLocalSign", profile, first), second,
                Seq(Minus, Apply(profile, second)), place));

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, type, Comma, Esc,
            OpenBracket, Call("DecidableEq", carrier), CloseBracket, Comma, Sp,
            places, Colon, Sp, Call("Finset", carrier), Comma, Esc,
            profile, Colon, Sp, carrier, Sp, To, Sp, signs, Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, carrier, Comma, Esc,
            first, Sp, InMacro, Sp, places, Sp, Land, Sp,
            second, Sp, InMacro, Sp, places, Sp, Land, Sp,
            first, Sp, Neq, Sp, second, Sp, Land, Sp,
            SignProduct(places, place, Apply(profile, place)), Sp, Eq, Sp, D(1),
            Sp, Rightarrow, Sp, Open,
            firstFlip, Sp, Eq, Sp, Minus, D(1), Sp, Land, Sp,
            firstFlip, Sp, Eq, Sp, secondFlip, Sp, Land, Sp,
            doubleFlip, Sp, Eq, Sp, D(1), Close, Dot));
    }

    private static Formula SignProduct(Formula places, Formula place, Formula value) =>
        Seq(Prod, Underscore, Grp(place, Sp, InMacro, Sp, places), Sp, value);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
