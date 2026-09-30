using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class ClausePreprocessorRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The total raw-word parser agrees with the fixed machine's exact clean physical-query output.",
        H("Total Clause Machine Word Refinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("pre-word-run"),
            DeclarationHandle.Create("D5/S0/Computability/ClausePreprocessorRefinement.pre_word_run"),
            H("Arbitrary source words, exact query, and rejection entry"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every Boolean word w, preparedFormula is its total source "
                    + "decoder result, defaulting to zero variables and one empty "
                    + "clause when decoding fails. preparedQuery is queryWord of "
                    + "the decoded raw formula, or the fixed dummyQuery on failure.")),
                Paragraph(Text(
                    "The fixed five-stack machine reaches exactly the clean haltList "
                    + "with preparedQuery within (4L plus 20)L plus 13 actual steps, "
                    + "where L is the input length. The output decodes in physical mode "
                    + "to preparedFormula, equals its complete physical encoding, and "
                    + "has only clauses of width at most three. Its length is at most "
                    + "that step bound times the fixed program push bound.")),
                Paragraph(Text(
                    "If the source decoder rejects, the actual run first reaches "
                    + "badInput with empty output and concrete input, header, scratch "
                    + "and query stacks within the same bound. Cleanup then produces "
                    + "the fixed zero-variable, one-empty-clause descriptor. The "
                    + "valid source for that same formula also produces dummyQuery; "
                    + "rejection is determined by the parser and phase, not output equality.")),
                Paragraph(Text(
                    "Phase-specific grammar predicates preserve acceptance through "
                    + "actual parsing, copying and restoration steps. Induction along "
                    + "a rejected terminating trace finds its badInput prefix. Accepted "
                    + "words use decoder soundness and the valid-source run. Deterministic "
                    + "terminal uniqueness identifies each output with the already bounded "
                    + "total run. Physical trace values, conventional counting-name "
                    + "conversion, oracle response materialization and the one-call "
                    + "protocol require additional results."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ClauseWordCodec")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ClauseMalformedCleanup")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ClausePreprocessorClock"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Presentation()
    {
        var w = Id("w");
        var query = Call("preparedQuery", w);
        var formula = Call("preparedFormula", w);
        var clauses = Call("snd", formula);
        var length = Call("length", w);
        var bound = Add(Multiply(Add(Multiply(Num(4), length), Num(20)), length), Num(13));
        var run = Call("Nonempty", Call("TM2OutputsInTime", Id("preMachine"), w,
            Call("some", query), bound));
        var decoded = Equal(Call("readWord", Id("true"), query), Call("some", formula));
        var encoded = Equal(query, Call("encodeWord", Id("true"), clauses));
        var width = All("c", clauses, new Formula.Relation(Call("length", Id("c")),
            FormulaRelationOperator.LessThanOrEqual, Num(3)));
        var growth = new Formula.Relation(Call("length", query),
            FormulaRelationOperator.LessThanOrEqual,
            Multiply(bound, Call("programPushBound", Call("m", Id("preMachine")))));
        var boolList = Call("List", Id("Bool"));
        var prefix = Call("Nonempty", Call("EvalsToInTime", Call("step", Id("preMachine")),
            Call("initList", Id("preMachine"), w),
            Call("some", Call("preCfg", Id("badInput"), Id("st"), Id("input"),
                Id("header"), Id("scratch"), Id("query"), Id("nil"))), bound));
        var failure = new Formula.Logic(Equal(Call("readWord", Id("false"), w), Id("none")),
            FormulaLogicOperator.Implies, Exists("st", Id("PreControl"),
                Exists("input", boolList, Exists("header", boolList,
                    Exists("scratch", boolList, Exists("query", boolList, prefix))))));
        return All("w", boolList, And(run, And(decoded, And(encoded,
            And(width, And(growth, failure))))));
    }
}
