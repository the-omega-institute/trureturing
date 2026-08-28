using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class BinaryCharacterProfileRankCardinalityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/CharacterSelection/"
            + "BinaryCharacterProfileRankCardinality."
            + "binary_character_profile_rank_cardinality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary-character span rank determines the realized profile count and every realized fiber size.",
        H("Binary Character Profile Rank Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-character-profile-rank-cardinality"),
                DeclarationHandle.Create(Declaration),
                H("Character rank controls profiles and fibers"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The group is finite abelian. Each binary character is a linear "
                            + "functional on the canonical quotient by doubles and is evaluated "
                            + "back on the original group.")),
                    Paragraph(Text(
                        "The joint profile is constructed componentwise from those characters. "
                            + "Its rank is the finite dimension of their linear span.")),
                    Paragraph(Text(
                        "All three conclusions are public: the kernel intersection, the power-of-two "
                            + "realized image count, and the uniform cardinality of every realized "
                            + "profile fiber."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula index = F.Id("I");
        Formula characters = F.Id("chi");
        Formula character = F.Id("c");
        Formula element = F.Id("g");
        Formula profileValue = F.Id("b");
        Formula field = Call("ZMod", D(2));
        Formula quotient = Call("ModN", group, D(2));
        Formula dual = Call("Dual", field, quotient);
        Formula characterFamily = Seq(index, Sp, To, Sp, dual);
        Formula profile = F.Id("Phi");
        Formula profileDefinition = Seq(
            Apply(Apply(profile, element), character), Sp, Colon, Eq, Sp,
            Apply(Apply(characters, character),
                Call("mkQ", D(2), element)));
        Formula span = F.Id("H");
        Formula rank = F.Id("r");
        Formula spanDefinition = Seq(
            span, Sp, Colon, Eq, Sp,
            Call("span", field, Call("range", characters)));
        Formula rankDefinition = Seq(
            rank, Sp, Colon, Eq, Sp, Call("finrank", field, span));
        Formula componentMap = Seq(
            Apply(characters, character), Sp, Circ, Sp, Call("mkQ", D(2)));
        Formula componentKernel = Call("ker", componentMap);
        Formula kernelClause = Seq(
            Call("ker", profile), Sp, Eq, Sp,
            Call("iInf", character, index, componentKernel));
        Formula twoToRank = new Formula.Power(D(2), rank);
        Formula imageClause = Seq(
            Call("card", Call("range", profile)), Sp, Eq, Sp, twoToRank);
        Formula fiber = Grp(OpenBrace,
            element, Colon, Sp, group, Sp, Mid, Sp,
            Apply(profile, element), Sp, Eq, Sp, profileValue,
            CloseBrace);
        Formula fiberClause = Seq(
            Forall, Sp, profileValue, Colon, Sp, Call("range", profile),
            Comma, Sp, Call("card", fiber), Sp, Eq, Sp,
            new Formula.Fraction(Call("card", group), twoToRank));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Comma, Sp, index, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            Typeclass("AddCommGroup", group), Comma, Sp,
            Typeclass("Fintype", group), Comma, Sp,
            Typeclass("Fintype", index), Comma, RowBreak, Grp(),
            characters, Colon, Sp, characterFamily, Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            profileDefinition, Comma, Sp, spanDefinition, Comma, Sp,
            rankDefinition, Close, SemiSpace, RowBreak, Grp(),
            kernelClause, Comma, Sp, imageClause, Comma, Sp,
            fiberClause, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
