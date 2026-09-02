using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class GoldenCharacterQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/GoldenCharacterQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quadratic character modulo five gives a binary quotient of unramified prime words.",
        H("Golden Character Quotient"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-character-quotient-specification"),
            DeclarationHandle.Create(Prefix + "golden_character_quotient_spec"),
            H("Golden character quotient specification"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Restrict every letter to a rational prime different from five. The "
                        + "Legendre symbol modulo five then takes values in the two integer "
                        + "units, and its product defines a homomorphism from the free monoid "
                        + "of prime words to this binary group.")),
                Paragraph(Text(
                    "Concatenation becomes multiplication, permutations do not change the "
                        + "value, and the value is negative one raised to the number of inert "
                        + "letters. The words [2, 3] and [2, 11] witness both quotient values.")),
                Paragraph(Text(
                    "The source passage does not define the full holonomy, observer rapidity, "
                        + "or commutator holonomy. No formal claim about forgetting those data "
                        + "is made here."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula ForEvery(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula TheoremFormula()
    {
        Formula wordType = Call("List", Id("UnramifiedPrime"));
        Formula word = Id("w");
        Formula first = Id("u");
        Formula second = Id("v");
        Formula holonomy = Apply("holFive", word);
        Formula quotientValue = Apply(
            "coe",
            Apply("holFiveQuotient", Apply("ofList", word)));

        Formula quotientClause = ForEvery(
            "w",
            wordType,
            Equal(quotientValue, holonomy));
        Formula multiplicativeClause = ForEvery(
            "u",
            wordType,
            ForEvery(
                "v",
                wordType,
                Equal(
                    Apply("holFive", Apply("append", first, second)),
                    Multiply(Apply("holFive", first), Apply("holFive", second)))));
        Formula permutationClause = ForEvery(
            "u",
            wordType,
            ForEvery(
                "v",
                wordType,
                new Formula.Logic(
                    Apply("Perm", first, second),
                    FormulaLogicOperator.Implies,
                    Equal(Apply("holFive", first), Apply("holFive", second)))));
        Formula parityClause = ForEvery(
            "w",
            wordType,
            Equal(
                holonomy,
                new Formula.Power(
                    new Formula.Negate(Num(1)),
                    Apply("inertCount", word))));
        Formula rangeClause = ForEvery(
            "w",
            wordType,
            new Formula.Logic(
                Equal(holonomy, Num(1)),
                FormulaLogicOperator.Or,
                Equal(holonomy, new Formula.Negate(Num(1)))));
        Formula characterWitnesses = And(
            Equal(Apply("goldenCharacter", Id("eleven")), Num(1)),
            Equal(Apply("goldenCharacter", Id("nineteen")), Num(1)),
            Equal(Apply("goldenCharacter", Id("two")), new Formula.Negate(Num(1))),
            Equal(Apply("goldenCharacter", Id("three")), new Formula.Negate(Num(1))));
        Formula wordWitnesses = And(
            Equal(Apply("holFive", Apply("word", Id("two"), Id("three"))), Num(1)),
            Equal(
                Apply("holFive", Apply("word", Id("two"), Id("eleven"))),
                new Formula.Negate(Num(1))));

        return FormulaDsl.Disp(And(
            quotientClause,
            multiplicativeClause,
            permutationClause,
            parityClause,
            rangeClause,
            characterWitnesses,
            wordWitnesses));
    }
}
