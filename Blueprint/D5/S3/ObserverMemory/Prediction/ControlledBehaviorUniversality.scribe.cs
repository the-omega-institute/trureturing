using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class ControlledBehaviorUniversalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite controlled realization maps uniquely onto the complete behavior quotient.",
        H("Controlled Behavior Universality"),
        Blocks(
            new DocumentBlock.Section(H("Local observation and choices"), Blocks(
                Paragraph(Text(
                    "For an event set E(o), its dependency support consists of events below some member of "
                    + "E(o). Intersecting a configuration with that support defines its local record. If equal "
                    + "local records give equal output q, realized-image factorization gives a unique decoder "
                    + "of q from those records. Composing q with any fixed choice map to sets of alphabet "
                    + "symbols preserves this locality. This implication uses the stated locality assumption; "
                    + "the event order alone does not impose it.")))),
            new DocumentBlock.Section(H("Arbitrary-output quotients on all words"), Blocks(
                Paragraph(Text(
                    "Let L be a prefix-closed language over an arbitrary alphabet and let q map legal words "
                    + "to an arbitrary output set Y. Extend q to every word by adjoining an illegal value, "
                    + "represented by Option(Y). The carrier of the quotient is the whole word space, including "
                    + "illegal words. Two words are equivalent when every continuation produces equal extended "
                    + "output.")),
                Paragraph(Text(
                    "The response profile is v maps to extended-q(wv). Equality of profiles is a kernel "
                    + "equivalence. Appending one letter preserves it because a continuation after that letter "
                    + "is itself a continuation of the original word. Quotient.map therefore defines the update "
                    + "on every class, and evaluation of the lifted profile at the empty word defines current "
                    + "output. Prefix closure implies that every extension of an illegal word remains illegal, "
                    + "so any illegal words have the same profile and appending a letter preserves their class.")),
                Paragraph(Text(
                    "For any deterministic state machine with a current-state decoder that gives the extended "
                    + "output on every word, equal reached states give equal states after every continuation. "
                    + "The DFA evaluation law for appended words then proves equality of all future outputs. "
                    + "Thus its state kernel refines the response equivalence. No finite-state assumption is "
                    + "needed for this minimality implication. The finite-carrier universal theorem in this module is a "
                    + "separate specialization; it is not needed to make updates on the all-word quotient "
                    + "total.")),
                Paragraph(Text(
                    "The language-valued predecessor is the Myhill-Nerode relation on all words recalled on "
                    + "page one of Kozen, On the Myhill-Nerode Theorem for Trees. Equality of arbitrary output "
                    + "profiles replaces equality of Boolean membership; the concatenation argument is "
                    + "unchanged.")))),
            new DocumentBlock.Section(H("Exact clocks require corresponding state capacity"), Blocks(
                Paragraph(Text(
                    "For a nonempty alphabet choose a letter a. The words consisting of zero through N copies "
                    + "of a have distinct exact lengths. In state_lower_bound_of_distinguishing_family, use "
                    + "these N+1 prefixes and the empty continuation for every pair. Any state decoder correct "
                    + "for length on this domain therefore needs at least N+1 states. Encoding these states in "
                    + "b fixed bits requires b at least the ceiling of log base two of N+1.")),
                Paragraph(Text(
                    "If the language contains words of unbounded length, exact length output requires "
                    + "infinitely many distinguishable states. For the full word language over a nonempty "
                    + "alphabet, apply the preceding bound with N equal to the purported finite state count. An "
                    + "empty alphabet or a bounded-length domain does not have this obstruction. Any clock "
                    + "register, external memory, or other interface used by the decoder is part of its state "
                    + "for this counting argument.")))),
            Describe.Lean(
                DescribeId.Create("controlled-behavior"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality."
                        + "controlledBehavior"),
                H("Controlled behavior records every finite-word readout"),
                StatementSource.FromAuthor(ControlledBehaviorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an input-indexed update, a readout, an initial state y, and every "
                        + "finite input word, controlledBehavior returns the readout of the "
                        + "state obtained by applying that word from left to right."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("controlled-behavior-has-a-universal-minimal-realization"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality."
                        + "controlled_behavior_universal_property"),
                H("Controlled behavior has a universal minimal realization"),
                StatementSource.FromAuthor(UniversalPropertyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite controlled state carrier with input-indexed updates "
                            + "and readout q. Let Z be the quotient by equality of every readout "
                            + "after every finite input word. Its projection, induced updates, "
                            + "and induced readout are defined directly from that behavior "
                            + "kernel.")),
                    Paragraph(Text(
                        "For any finite realization W reached surjectively from Y, commuting "
                            + "with every update and with the readout, there is a unique "
                            + "surjective factor h from W to Z. It factors the canonical "
                            + "projection, intertwines every realized update, and preserves the "
                            + "readout. Surjectivity gives card(Z) at most card(W).")),
                    Paragraph(Text(
                        "The factor is built from a right inverse of the realization map. "
                            + "Commutation along input words proves that different chosen "
                            + "preimages have equal complete behavior. Surjectivity of the "
                            + "canonical quotient projection proves surjectivity of h, while "
                            + "surjectivity onto W proves all equations and uniqueness pointwise.")),
                    Paragraph(Text(
                        "The quotient-to-range equivalence identifies a behavior class with its "
                            + "realized response profile. The cardinal inequality follows from "
                            + "surjectivity of the factor, independently of how the states are named."))),
                DescribeRole.Theorem))));

    private static Formula Typed(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Card(Formula type) =>
        Seq(Operatorname, Grp(F.Id("card")), Open, type, Close);

    private static Formula ControlledBehaviorFormula()
    {
        Formula input = F.Id("U");
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula initial = F.Id("y");
        Formula word = F.Id("word");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula wordType = Call("List", input);
        Formula behavior = Call("controlledBehavior", update, readout, initial, word);
        Formula evolved = Call("runWord", update, word, initial);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, input, Comma, Sp, state, Comma, Sp, output,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            update, Colon, Sp,
            new Formula.TypeArrow(input, new Formula.TypeArrow(state, state)), Comma, Sp,
            readout, Colon, Sp, new Formula.TypeArrow(state, output), Comma, Sp,
            initial, Colon, Sp, state, Comma, RowBreak, Grp(),
            Forall, Sp, word, Colon, Sp, wordType, Comma, Sp,
            behavior, Sp, Eq, Sp, Apply(readout, evolved), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula UniversalPropertyFormula()
    {
        Formula yType = F.Id("Y");
        Formula inputType = F.Id("U");
        Formula outputType = F.Id("O");
        Formula realizedType = F.Id("W");
        Formula completionType = F.Id("Z");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula realization = F.Id("r");
        Formula realizedUpdate = F.Id("G");
        Formula realizedReadout = F.Id("o");
        Formula projection = Pi;
        Formula completedUpdate = Seq(Overline, Grp(F.Id("F")));
        Formula completedReadout = Seq(Overline, Grp(F.Id("q")));
        Formula factor = F.Id("h");
        Formula input = F.Id("u");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, yType, Comma, Sp, inputType, Comma, Sp, outputType,
            Comma, Sp, realizedType, Comma, RowBreak, Grp(),
            Typeclass("Fintype", yType), Comma, Sp,
            Typeclass("Fintype", realizedType), Comma, RowBreak,
            Typed("F", new Formula.TypeArrow(inputType,
                new Formula.TypeArrow(yType, yType))), Comma, Sp,
            Typed("q", new Formula.TypeArrow(yType, outputType)), Comma, RowBreak,
            Typed("r", new Formula.TypeArrow(yType, realizedType)), Comma, Sp,
            Typed("G", new Formula.TypeArrow(inputType,
                new Formula.TypeArrow(realizedType, realizedType))), Comma, Sp,
            Typed("o", new Formula.TypeArrow(realizedType, outputType)), Comma, RowBreak,
            Call("Surjective", realization), Sp, Rightarrow, Sp,
            Open, Forall, Sp, input, InMacro, Sp, inputType, Comma, Sp,
            realization, Sp, Circ, Sp, Apply(update, input), Sp, Eq, Sp,
            Apply(realizedUpdate, input), Sp, Circ, Sp, realization, Close,
            Sp, Rightarrow, Sp,
            readout, Sp, Eq, Sp, realizedReadout, Sp, Circ, Sp, realization,
            Sp, Rightarrow, RowBreak,
            Open, Exists, Bang, Sp, factor, Colon, Sp, realizedType, Sp, To, Sp,
            completionType, Comma, Sp, Call("Surjective", factor), Sp, Land, Sp,
            projection, Sp, Eq, Sp, factor, Sp, Circ, Sp, realization, Sp, Land,
            RowBreak, Open, Forall, Sp, input, InMacro, Sp, inputType, Comma, Sp,
            factor, Sp, Circ, Sp, Apply(realizedUpdate, input), Sp, Eq, Sp,
            Apply(completedUpdate, input), Sp, Circ, Sp, factor, Close, Sp, Land, RowBreak,
            completedReadout, Sp, Circ, Sp, factor, Sp, Eq, Sp, realizedReadout,
            Close, Sp, Land, Sp,
            Card(completionType), Sp, Leq, Sp, Card(realizedType), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
