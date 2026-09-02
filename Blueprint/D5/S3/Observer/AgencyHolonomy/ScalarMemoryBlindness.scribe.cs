using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class ScalarMemoryBlindnessDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Observer/AgencyHolonomy/ScalarMemoryBlindness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar Euler behavior forgets every hidden-memory coordinate.",
        H("Scalar Memory Blindness"),
        Blocks(Describe.Lean(
            DescribeId.Create("scalar-memory-blindness"),
            DeclarationHandle.Create(Handle + "scalar_memory_blindness"),
            H("Every finite scalar behavior is blind to memory"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The layer ranges over the source-fixed three residual local factors. "
                        + "The spectral parameter and the entire prime-indexed channel "
                        + "family remain public parameters.")),
                Paragraph(Text(
                    "Each prime step applies the imported Fibonacci substitution to the "
                        + "two-dimensional memory, adds the local-factor channel forcing, "
                        + "and multiplies the scalar by that same local factor.")),
                Paragraph(Text(
                    "The scalar coordinate therefore evolves without reading memory. "
                        + "Induction over every finite prime word gives equal scalar "
                        + "readouts, and the canonical controlled-behavior quotient "
                        + "identifies the full memory fiber over each scalar."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula finTwo = Call("Fin", D(2));
        Formula finThree = Call("Fin", D(3));
        Formula primes = Seq(F.Id("Nat"), Dot, F.Id("Primes"));
        Formula memoryType = Arrow(finTwo, complex);
        Formula channelType = Arrow(primes, memoryType);
        Formula wordType = Call("List", primes);
        Formula depth = F.Id("r");
        Formula spectral = F.Id("s");
        Formula channel = F.Id("v");
        Formula scalar = F.Id("z");
        Formula scalarPrime = F.Id("zprime");
        Formula word = F.Id("w");
        Formula memory = F.Id("m");
        Formula memoryPrime = F.Id("mprime");
        Formula update = Call("scalarMemoryUpdate", depth, spectral, channel);

        Formula State(Formula hidden, Formula visible) =>
            Seq(Open, hidden, Comma, Sp, visible, Close);
        Formula ScalarAfter(Formula hidden, Formula visible) => Call(
            "snd",
            Call("runWord", update, word, State(hidden, visible)));
        Formula Projection(Formula hidden, Formula visible) => Call(
            "completionProjection",
            update,
            F.Id("snd"),
            State(hidden, visible));

        Formula finiteWordBlindness = ForAll(
            [
                Bound("w", wordType),
                Bound("m", memoryType),
                Bound("mprime", memoryType),
            ],
            Equal(
                ScalarAfter(memory, scalar),
                ScalarAfter(memoryPrime, scalarPrime)));
        Formula fiberCollapse = ForAll(
            [Bound("m", memoryType), Bound("mprime", memoryType)],
            Equal(
                Projection(memory, scalar),
                Projection(memoryPrime, scalar)));
        Formula scalarCondition = ForAll(
            [Bound("z", complex), Bound("zprime", complex)],
            Implies(
                Equal(scalar, scalarPrime),
                And(finiteWordBlindness, fiberCollapse)));

        return Disp(ForAll(
            [
                Bound("r", finThree),
                Bound("s", complex),
                Bound("v", channelType),
            ],
            scalarCondition));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula ForAll(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
