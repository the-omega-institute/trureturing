using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class WordProbabilityTraceRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite instrument word has matching operational, Schrödinger-trace, and Heisenberg-effect probabilities.",
        H("Word-Probability Trace Representation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("word-probability-has-the-two-trace-representations"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/WordProbabilityTraceRepresentation."
                        + "word_probability_trace_representation"),
                H("Word probability has Schrödinger and Heisenberg trace forms"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite word of completely positive instrument branches, the "
                            + "operational probability is evaluated recursively on the current "
                            + "subnormalized branch state. It equals the trace after the full "
                            + "Schrödinger fold.")),
                    Paragraph(Text(
                        "A supplied trace-duality law pulls each branch back in reverse order. "
                            + "The resulting effect is the imported canonical sequential word "
                            + "effect, obtained by applying the Heisenberg branches to the "
                            + "identity effect.")),
                    Paragraph(Text(
                        "The formula displays the canonical conversion from the raw Hermitian "
                            + "word effect to the C-star matrix carrier used by the branch maps. "
                            + "This is a data-preserving matrix equivalence, not an implicit "
                            + "change of carrier."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), alphabet = F.Id("A"), generator = F.Id("g");
        Formula instrument = F.Id("I"), instrumentDual = F.Id("J");
        Formula state = F.Id("X"), effect = F.Id("E");
        Formula rho = Rho, word = F.Id("w");
        Formula nat = F.Id("Nat"), type = Call("Type");
        Formula indices = Call("Fin", d);
        Formula matrix = Call("MatrixAlgebra", indices);
        Formula branch = Call("CompletelyPositiveMap", matrix, matrix);
        Formula branchFamily = Arrow(alphabet, branch);
        Formula density = Call("DensityState", indices);
        Formula words = Call("List", alphabet);
        Formula rhoValue = Call("val", rho);

        Formula InstrumentAt(Formula branchName, Formula input) =>
            Apply(Apply(instrument, branchName), input);
        Formula DualAt(Formula branchName, Formula input) =>
            Apply(Apply(instrumentDual, branchName), input);

        Formula duality = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("g", alphabet), Bound("X", matrix), Bound("E", matrix)],
            Equal(
                Call("Tr", Multiply(InstrumentAt(generator, state), effect)),
                Call("Tr", Multiply(state, DualAt(generator, effect)))));

        Formula schrodingerWord = Call("instrumentWordFold", instrument, rhoValue, word);
        Formula wordEffect = Call(
            "sequentialWordEffect",
            Call("heisenbergOnHermitianFamily", instrumentDual),
            word);
        Formula bridgedEffect = Call("ofMatrix", Call("val", wordEffect));
        Formula probability = Call(
            "operationalWordProbability",
            instrument,
            rhoValue,
            word);
        Formula schrodingerTrace = Call("Tr", schrodingerWord);
        Formula heisenbergTrace = Call(
            "Tr",
            Multiply(rhoValue, bridgedEffect));
        Formula conclusion = And(
            Equal(probability, schrodingerTrace),
            Equal(schrodingerTrace, heisenbergTrace));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("d", nat), Bound("A", type),
                Bound("I", branchFamily), Bound("J", branchFamily),
                Bound("rho", density), Bound("w", words)],
            new Formula.Logic(duality, FormulaLogicOperator.Implies, conclusion)));
    }
}
