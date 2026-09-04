using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class ModFiveCharacterWordQuotientDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/ModFiveCharacterWordQuotient."
            + "mod_five_character_word_scalar_quotient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar product identifies two distinct directed mod-five character words.",
        H("Mod-Five Character Word Scalar Quotient"),
        Blocks(Describe.Lean(
            DescribeId.Create("mod-five-character-word-scalar-quotient"),
            DeclarationHandle.Create(Declaration),
            H("The scalar quotient forgets character-word direction"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For offsets zero and two, the quadratic character modulo five sends "
                        + "residues one and two to the directed words (1,-1) and (-1,1).")),
                Paragraph(Text(
                    "The complete residue image is the displayed five-word finite set. "
                        + "The two mixed-sign words are distinct but both have scalar "
                        + "product -1, so pair multiplication is not injective on this "
                        + "character-word image."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula integers = F.Seq(F.Mathbb, F.Grp(F.Id("Z")));
        Formula residues = Call("ZMod", F.D(5));
        Formula pairType = F.Seq(integers, F.Sp, F.Times, F.Sp, integers);
        Formula wordsType = Call("Finset", pairType);
        Formula n = F.Id("n");
        Formula word = F.Id("w");
        Formula characterWord = F.Id("characterWord");
        Formula scalarProduct = F.Id("scalarProduct");
        Formula validWords = F.Id("validWords");
        Formula one = F.D(1);
        Formula two = F.D(2);
        Formula negativeOne = new Formula.Negate(one);

        Formula Pair(Formula first, Formula second) =>
            F.Seq(F.Open, first, F.Comma, F.Sp, second, F.Close);
        Formula Character(Formula residue) =>
            Call("legendreSym", F.D(5), Call("val", residue));
        Formula CharacterWord(Formula residue) =>
            Call("characterWord", residue);
        Formula Scalar(Formula value) =>
            Call("scalarProduct", value);

        Formula characterWordDefinition = Lambda(
            n,
            residues,
            Pair(
                Character(n),
                Character(F.Seq(n, F.Sp, F.Plus, F.Sp, two))));
        Formula scalarProductDefinition = Lambda(
            word,
            pairType,
            F.Seq(
                Call("fst", word),
                F.Sp,
                F.Times,
                F.Sp,
                Call("snd", word)));
        Formula validWordsDefinition = Call(
            "image",
            characterWord,
            Call("univ", residues));

        Formula forward = CharacterWord(one);
        Formula reverse = CharacterWord(two);
        Formula mixedWords = new Formula.SetLiteral([
            Pair(F.D(0), negativeOne),
            Pair(one, negativeOne),
            Pair(negativeOne, one),
            Pair(negativeOne, F.D(0)),
            Pair(one, one),
        ]);

        return F.Disp(new Formula.Aligned([
            Let(characterWord, Arrow(residues, pairType), characterWordDefinition),
            Let(scalarProduct, Arrow(pairType, integers), scalarProductDefinition),
            Let(validWords, wordsType, validWordsDefinition),
            F.Seq(
                F.Open,
                All(
                    Equal(forward, Pair(one, negativeOne)),
                    Equal(reverse, Pair(negativeOne, one)),
                    NotEqual(forward, reverse),
                    Equal(Scalar(forward), negativeOne),
                    Equal(Scalar(reverse), negativeOne),
                    Equal(Scalar(forward), Scalar(reverse)),
                    Equal(validWords, mixedWords),
                    new Formula.Not(Call("InjOn", scalarProduct, Call("coe", validWords)))),
                F.Close),
        ]));
    }

    private static Formula Let(Formula name, Formula type, Formula value) =>
        F.Seq(
            F.Operatorname,
            F.Grp(F.Id("let")),
            F.Sp,
            name,
            F.Colon,
            F.Sp,
            type,
            F.Sp,
            F.Eq,
            F.Sp,
            value,
            F.Comma);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        F.Seq(
            F.Open,
            name,
            F.Colon,
            F.Sp,
            type,
            F.Sp,
            F.Mapsto,
            F.Sp,
            body,
            F.Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        }

        return result;
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
