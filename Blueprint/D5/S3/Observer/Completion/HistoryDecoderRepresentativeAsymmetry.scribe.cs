using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class HistoryDecoderRepresentativeAsymmetryDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Completion/HistoryDecoderRepresentativeAsymmetry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A forgetful completion map may choose one source representative per scalar fiber, "
            + "but a nontrivial fiber prevents exact reconstruction of every history.",
        H("History Decoder and Fiber Representatives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-exact-history-decoder"),
                DeclarationHandle.Create(DeclarationPrefix + "no_exact_history_decoder"),
                H("No exact history decoder"),
                StatementSource.FromAuthor(DecoderFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The forgetful map is supplied directly. A pair of distinct memory "
                            + "states in one scalar fiber witnesses the information loss. Any "
                            + "left inverse would make the forgetful map injective and would "
                            + "therefore identify that distinct pair.")),
                    Paragraph(Text(
                        "Surjectivity states that every scalar fiber is inhabited. Classical "
                            + "choice then selects one memory representative in every fiber, "
                            + "giving a right inverse. This section does not recover all memory "
                            + "states and so does not contradict the decoder obstruction."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula DecoderFormula()
    {
        Formula memory = F.Id("Memory");
        Formula scalar = F.Id("Scalar");
        Formula forget = F.Id("forget");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula decoder = F.Id("decoder");
        Formula representative = F.Id("representative");

        Formula memoryEscape = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("first", memory), Bound("second", memory)],
            And(
                NotEqual(first, second),
                Equal(Call("forget", first), Call("forget", second))));
        Formula allFibersRealized = Call("Surjective", forget);
        Formula noDecoder = new Formula.Not(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("decoder", Arrow(scalar, memory))],
            Call("LeftInverse", decoder, forget)));
        Formula representativeSection = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("representative", Arrow(scalar, memory))],
            Call("RightInverse", representative, forget));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Memory", F.Id("Type")),
                Bound("Scalar", F.Id("Type")),
                Bound("forget", Arrow(memory, scalar)),
            ],
            new Formula.Logic(
                And(memoryEscape, allFibersRealized),
                FormulaLogicOperator.Implies,
                And(noDecoder, representativeSection))));
    }
}
