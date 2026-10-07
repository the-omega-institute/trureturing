using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciTerminalSamplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var m = Id("m"); var f = Id("f"); var h = Id("h"); var c = Id("c");
        var e = Id("e"); var w = Id("w"); var a = Id("a");
        var t = Id("t"); var x = Id("x"); var q = Id("q");
        var d = Call("C", m, f, h); var size = new Formula.Power(Num(2), h);
        var eval = Call("sample", m, a, f, h, c);
        var returned = Equal(eval, Call("some", w, e));
        var draw = Call("Draw", h, d, c, t, x);
        var output = Call("Return", m, f, h, c, w);
        Formula All(string name, Formula domain, Formula body) =>
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
        Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
        Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
        Formula Mass(Formula set) => Call("mu", set);
        Formula Inv(Formula value) => new Formula.Fraction(Num(1), value);
        var statement = All("m", Id("N"), All("f", Id("N"), All("h", Id("N"),
            All("c", Id("N"), All("e", Id("N"), All("w", Call("Words", h), All("a", Id("Tape"),
            new Formula.Aligned([
                new Formula.Logic(Call("Run", m, a, f, h, c, w, e), FormulaLogicOperator.Iff, returned),
                Implies(returned, And(Call("Legal", m, f, h, w),
                    And(new Formula.Relation(c, FormulaRelationOperator.LessThanOrEqual, e),
                        And(Call("Replay", m, a, f, h, c, w, e),
                            Equal(Mass(Call("Intersection", Call("Cylinder", c, e, a),
                                Call("Result", m, f, h, c, w, e))),
                                new Formula.Power(Inv(Num(2)), Subtract(e, c))))))),
                All("t", Id("N"), All("x", Call("Fin", size), new Formula.Logic(
                    Equal(Call("draw", h, d, c, a), Call("some", t, x)), FormulaLogicOperator.Iff,
                    And(Call("AcceptedAt", h, d, c, a, t),
                        Equal(Call("readBlock", h, Add(c, Multiply(t, h)), a), x))))),
                All("t", Id("N"), All("x", Call("Fin", size), Implies(
                    new Formula.Relation(x, FormulaRelationOperator.LessThan, d),
                    And(Call("MeasurableSet", draw), Equal(Mass(draw), new Formula.Fraction(
                        new Formula.Power(new Formula.Fraction(Subtract(size, d), size), t), size)))))),
                All("x", Call("Fin", size), Implies(new Formula.Relation(x, FormulaRelationOperator.LessThan, d),
                    And(Call("MeasurableSet", Call("AcceptedValue", h, d, c, x)),
                        Equal(Mass(Call("AcceptedValue", h, d, c, x)), Inv(d))))),
                And(Call("MeasurableSet", Call("RejectedForever", h, d, c)),
                    Equal(Mass(Call("RejectedForever", h, d, c)), Num(0))),
                All("q", Id("N"), Implies(Equal(h, Add(q, Num(1))),
                    And(Call("MeasurableSet", Call("ZeroBranch", m, f, h, c)),
                        Equal(Mass(Call("ZeroBranch", m, f, h, c)),
                            new Formula.Fraction(Call("C", m, m, q), d))))),
                And(Call("MeasurableSet", Call("Result", m, f, h, c, w, e)), Call("MeasurableSet", output)),
                Call("MeasurableSample", m, f, h, c),
                Implies(Call("Illegal", m, f, h, w), Equal(Mass(output), Num(0))),
                Equal(Mass(Call("SuccessfulLegalReturn", m, f, h, c)), Num(1))
            ]))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
        "Finite first-hit fair-bit executions return native legal words almost surely.",
        H("Terminal Fair-Bit Sampling"),
        Blocks(
            Paragraph(Text(
                "A word is a literal Boolean function on Fin h. The native scanner has fuel "
                + "further consecutive true bits available; false resets fuel to maxTrue, and "
                + "true decreases positive fuel. CompletionCount is the cardinality of this "
                + "native completion layer. The original order k and tail length s correspond "
                + "to maxTrue=k-1 and fuel=k-1-s. The output budget h and source cursor are separate.")),
            Paragraph(Text(
                "A draw decodes consecutive h-bit blocks from one iid fair Boolean tape. It "
                + "rejects integers outside the completion range and keeps the first accepted "
                + "integer. Every retry advances the source cursor by h while preserving the "
                + "output state. Acceptance emits one bit, advances past its block, and reduces "
                + "the remaining output budget. The zero threshold is the count after a false bit.")),
            Describe.Lean(
                DescribeId.Create("terminal-fair-bit-execution-cylinders"),
                DeclarationHandle.Create(
                    "D5/S0/Tower/DBonacci/TerminalSampling.terminal_sampling_execution_cylinders"),
                H("Literal executions and consumed-source cylinders"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite Run relation and partial sample evaluator return the same "
                        + "word and final cursor. Returned words pass the native scanner, and "
                        + "agreement on the consumed source interval preserves the full result. "
                        + "A consumed interval of length L has fair mass 2^(-L).")),
                    Paragraph(Text(
                        "In the formula, N denotes natural numbers, Words(h) is Fin h to Bool, "
                        + "C(m,f,h) is completionCount, and mu is fairTape. Legal and Illegal mean "
                        + "the native scanner returns true and false. Result fixes word and final "
                        + "cursor; Return existentially quantifies the final cursor. Draw fixes retry "
                        + "and accepted integer; AcceptedValue existentially quantifies retry. "
                        + "RejectedForever means draw is none. ZeroBranch is the union of draws "
                        + "whose integer is below C(m,m,h-1). Cylinder is traceCylinder. Replay "
                        + "quantifies every tape agreeing on [c,e), preserving sample's full result. "
                        + "MeasurableSample uses the discrete Option codomain. SuccessfulLegalReturn "
                        + "is the event that some word and finite cursor are returned and that word "
                        + "is native legal. All rows of the displayed statement hold jointly.")),
                    Paragraph(Text(
                        "Writing D for the completion count and Q=2^h, acceptance of a specified "
                        + "integer at retry t has mass ((Q-D)/Q)^t/Q. Summing the disjoint retry "
                        + "events gives each accepted integer mass 1/D. D is positive and at most "
                        + "Q by the native cardinality results. Infinite rejection has mass zero.")),
                    Paragraph(Text(
                        "Every returned-word event is measurable. Illegal words have empty "
                        + "return events. A countable simultaneous acceptance event at all fixed "
                        + "states and cursors, followed by induction on h, proves whole termination "
                        + "almost surely. At h=0 the evaluator returns the unique empty word "
                        + "without drawing a branch. The denotation is noncomputable and partial; "
                        + "it supplies no deterministic uniform retry or fair-bit bound."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/DBonacci/Values"))]));
    }
}
