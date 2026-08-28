using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class BinaryCharacterSemanticRedundancyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/CharacterSelection/BinaryCharacterSemanticRedundancy."
            + "binary_character_semantic_redundancy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Character-span rank separates semantic profile bits from dependent parity checks.",
        H("Binary Character Semantic Redundancy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-character-semantic-redundancy"),
                DeclarationHandle.Create(Declaration),
                H("Semantic information and transmission redundancy separate"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Binary characters are linear functionals on the canonical quotient "
                            + "of a finite abelian group by doubles. Their joint profile and "
                            + "coefficient relation space are constructed from that family.")),
                    Paragraph(Text(
                        "The character-span rank counts independent profile bits, while the "
                            + "kernel of coefficient synthesis counts role relations.")),
                    Paragraph(Text(
                        "Adjoining a character already in the span preserves the realized "
                            + "profile count, adds one independent relation, and exposes a "
                            + "parity check with coefficient one on the new coordinate."))),
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
        Formula coordinate = F.Id("i");
        Formula extendedCoordinate = F.Id("j");
        Formula element = F.Id("g");
        Formula characters = F.Id("chi");
        Formula dependent = F.Id("eta");
        Formula extendedCharacters = F.Id("chiPlus");
        Formula originalProfile = F.Id("Phi");
        Formula extendedProfile = F.Id("PhiPlus");
        Formula roleSpace = F.Id("H");
        Formula relations = F.Id("R");
        Formula extendedRelations = F.Id("RPlus");
        Formula rank = F.Id("r");
        Formula check = F.Id("a");
        Formula field = Call("ZMod", D(2));
        Formula quotient = Call("ModN", group, D(2));
        Formula dual = Call("Dual", field, quotient);
        Formula optionIndex = Call("Option", index);
        Formula characterFamily = Seq(index, Sp, To, Sp, dual);
        Formula span = Call("span", field, Call("range", characters));
        Formula dependentPremise = Seq(dependent, Sp, InMacro, Sp, span);
        Formula extendedNone = Seq(
            Apply(extendedCharacters, F.Id("none")), Sp, Colon, Eq, Sp, dependent);
        Formula extendedSome = Seq(
            Forall, Sp, coordinate, Colon, Sp, index, Comma, Sp,
            Apply(extendedCharacters, Apply(F.Id("some"), coordinate)),
            Sp, Colon, Eq, Sp, Apply(characters, coordinate));
        Formula originalProfileDefinition = Seq(
            Apply(Apply(originalProfile, element), coordinate),
            Sp, Colon, Eq, Sp,
            Apply(Apply(characters, coordinate), Call("mkQ", D(2), element)));
        Formula extendedProfileDefinition = Seq(
            Apply(Apply(extendedProfile, element), extendedCoordinate),
            Sp, Colon, Eq, Sp,
            Apply(Apply(extendedCharacters, extendedCoordinate),
                Call("mkQ", D(2), element)));
        Formula roleSpaceDefinition = Seq(
            roleSpace, Sp, Colon, Eq, Sp, span);
        Formula rankDefinition = Seq(
            rank, Sp, Colon, Eq, Sp, Call("finrank", field, roleSpace));
        Formula relationsDefinition = Seq(
            relations, Sp, Colon, Eq, Sp,
            Call("ker", Call("linearCombination", field, characters)));
        Formula extendedRelationsDefinition = Seq(
            extendedRelations, Sp, Colon, Eq, Sp,
            Call("ker", Call("linearCombination", field, extendedCharacters)));
        Formula imageClause = Seq(
            Call("card", Call("range", originalProfile)), Sp, Eq, Sp,
            new Formula.Power(D(2), rank));
        Formula relationDimensionClause = Seq(
            Call("finrank", field, relations), Sp, Eq, Sp,
            Call("card", index), Sp, Minus, Sp, rank);
        Formula unchangedProfilesClause = Seq(
            Call("card", Call("range", extendedProfile)), Sp, Eq, Sp,
            Call("card", Call("range", originalProfile)));
        Formula extraRelationClause = Seq(
            Call("finrank", field, extendedRelations), Sp, Eq, Sp,
            Call("finrank", field, relations), Sp, Plus, Sp, D(1));
        Formula explicitCheckClause = Seq(
            Exists, Sp, check, Colon, Sp, optionIndex, Sp, To, Sp, field,
            Comma, Sp, check, Sp, InMacro, Sp, extendedRelations,
            Sp, Land, Sp, Apply(check, F.Id("none")), Sp, Eq, Sp, D(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Comma, Sp, index, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            Typeclass("AddCommGroup", group), Comma, Sp,
            Typeclass("Fintype", group), Comma, Sp,
            Typeclass("Fintype", index), Comma, RowBreak, Grp(),
            characters, Colon, Sp, characterFamily, Comma, Sp,
            dependent, Colon, Sp, dual, Comma, RowBreak, Grp(),
            dependentPremise, Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            extendedCharacters, Colon, Sp, optionIndex, Sp, To, Sp, dual,
            Comma, Sp, extendedNone, Comma, Sp, extendedSome,
            Comma, RowBreak, Grp(),
            originalProfileDefinition, Comma, Sp,
            extendedProfileDefinition, Comma, RowBreak, Grp(),
            roleSpaceDefinition, Comma, Sp, rankDefinition,
            Comma, Sp, relationsDefinition, Comma, RowBreak, Grp(),
            extendedRelationsDefinition, Close, SemiSpace, RowBreak, Grp(),
            imageClause, Sp, Land, RowBreak, Grp(),
            relationDimensionClause, Sp, Land, RowBreak, Grp(),
            unchangedProfilesClause, Sp, Land, RowBreak, Grp(),
            extraRelationClause, Sp, Land, RowBreak, Grp(),
            explicitCheckClause, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
