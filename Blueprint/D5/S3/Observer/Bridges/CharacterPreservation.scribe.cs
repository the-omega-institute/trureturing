using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class CharacterPreservationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Bridges/CharacterPreservation.character_preservation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An equivariant real-linear bridge preserves both reflection characters and has no "
            + "nonzero response of the opposite character.",
        H("Reflection Character Preservation"),
        Blocks(Describe.Lean(
            DescribeId.Create("character-preservation"),
            DeclarationHandle.Create(Declaration),
            H("Equivariant bridges preserve reflection characters"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let the configuration and response carriers be real modules. The two "
                        + "linear reflections act on their respective carriers, and the "
                        + "linear bridge intertwines those actions.")),
                Paragraph(Text(
                    "Fixed configurations map to fixed responses, while negated "
                        + "configurations map to negated responses. A response lying in the "
                        + "opposite character sector is therefore zero."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula configuration = F.Id("C");
        Formula response = F.Id("Z");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula configReflection = F.Id("configReflection");
        Formula responseReflection = F.Id("responseReflection");
        Formula bridge = F.Id("bridge");
        Formula linearConfigEnd = Call("LinearMap", real, configuration, configuration);
        Formula linearResponseEnd = Call("LinearMap", real, response, response);
        Formula linearBridge = Call("LinearMap", real, configuration, response);

        Formula evenMaps = CharacterClause(
            configuration, configReflection, responseReflection, bridge,
            negateInput: false, negateOutput: false, forceZero: false);
        Formula oddMaps = CharacterClause(
            configuration, configReflection, responseReflection, bridge,
            negateInput: true, negateOutput: true, forceZero: false);
        Formula evenExcludesOdd = CharacterClause(
            configuration, configReflection, responseReflection, bridge,
            negateInput: false, negateOutput: true, forceZero: true);
        Formula oddExcludesEven = CharacterClause(
            configuration, configReflection, responseReflection, bridge,
            negateInput: true, negateOutput: false, forceZero: true);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(Seq(configuration, Comma, Sp, response), type), Comma),
            Seq(
                Grp(), Typeclass("AddCommGroup", configuration), Comma, Sp,
                Typeclass("Module", real, configuration), Comma, Sp,
                Typeclass("AddCommGroup", response), Comma, Sp,
                Typeclass("Module", real, response), Comma),
            Seq(
                Grp(), Typed(configReflection, linearConfigEnd), Comma, Sp,
                Typed(responseReflection, linearResponseEnd), Comma, Sp,
                Typed(bridge, linearBridge), Comma),
            Seq(
                Grp(), QualifiedCall("Function", "Semiconj", bridge,
                    configReflection, responseReflection), Sp, Rightarrow),
            Seq(Grp(), Open, evenMaps, Close, Sp, Land),
            Seq(Grp(), Open, oddMaps, Close, Sp, Land),
            Seq(Grp(), Open, evenExcludesOdd, Close, Sp, Land),
            Seq(Grp(), Open, oddExcludesEven, Close, Dot),
        ]));
    }

    private static Formula CharacterClause(
        Formula configuration,
        Formula configReflection,
        Formula responseReflection,
        Formula bridge,
        bool negateInput,
        bool negateOutput,
        bool forceZero)
    {
        Formula x = F.Id("x");
        Formula bridgeAtX = Call("apply", bridge, x);
        Formula inputCharacter = Relation(
            Call("apply", configReflection, x),
            negateInput ? new Formula.Negate(x) : x);
        Formula outputCharacter = Relation(
            Call("apply", responseReflection, bridgeAtX),
            negateOutput ? new Formula.Negate(bridgeAtX) : bridgeAtX);
        Formula body = forceZero
            ? new Formula.Logic(
                inputCharacter,
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    outputCharacter,
                    FormulaLogicOperator.Implies,
                    Relation(bridgeAtX, D(0))))
            : new Formula.Logic(
                inputCharacter,
                FormulaLogicOperator.Implies,
                outputCharacter);

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("x"), configuration)],
            body);
    }

    private static Formula Relation(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula QualifiedCall(
        string qualifier, string name, params Formula[] arguments) =>
        new Formula.Apply(
            Seq(F.Id(qualifier), Dot, F.Id(name)),
            [.. arguments]);
}
