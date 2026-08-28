using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class CanonicalPredictiveStateSufficiencyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical conditional-future-law state makes the complete past and future conditionally independent.",
        H("Canonical Predictive-State Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-predictive-state-is-sufficient"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/"
                        + "CanonicalPredictiveStateSufficiency."
                        + "canonical_predictive_state_is_sufficient"),
                H("The predictive state retains every past influence on the future"),
                StatementSource.FromAuthor(SufficiencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Past and Future are finite alphabets. The process is constructed from a "
                            + "past prior and its conditional future PMF channel.")),
                    Paragraph(Text(
                        "The map epsilon is the canonical range factorization of the complete "
                            + "conditional future law, matching the repository's causal-state "
                            + "carrier. The displayed cross-product equality is the finite joint-law "
                            + "criterion for conditional independence of past and future given S.")),
                    Paragraph(Text(
                        "The proof identifies the induced law with a channel-generated Markov law "
                            + "and applies the frozen Markov channel theorem. No positive-support "
                            + "condition on the past prior is required."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

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

    private static Formula Assign(Formula left, Formula right) =>
        Seq(left, Sp, Colon, Eq, Sp, right);

    private static Formula SufficiencyFormula()
    {
        Formula pastType = F.Id("Past");
        Formula futureType = F.Id("Future");
        Formula prior = Pi;
        Formula futureLaw = F.Id("K");
        Formula stateType = F.Id("S");
        Formula stateMap = Varepsilon;
        Formula jointLaw = F.Id("J");
        Formula past = F.Id("h");
        Formula state = F.Id("s");
        Formula future = F.Id("f");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula stateCarrier = Call("range", futureLaw);
        Formula triple = Call("Triple", past, state, future);
        Formula pastState = Call("Pair", past, state);
        Formula stateFuture = Call("Pair", state, future);
        Formula yFirst = Call("yFirstLaw", jointLaw);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, pastType, Comma, Sp, futureType, Colon, Sp, type, Comma, Sp,
            Typeclass("Fintype", pastType), Comma, Sp,
            Typeclass("Fintype", futureType), Comma,
            RowBreak, Grp(),
            prior, Colon, Sp, Call("PMF", pastType), Comma, Sp,
            futureLaw, Colon, Sp, pastType, Sp, To, Sp, Call("PMF", futureType), Comma,
            RowBreak, Grp(),
            Assign(stateType, stateCarrier), Comma, Sp,
            Assign(Seq(stateMap, Colon, Sp, pastType, Sp, To, Sp, stateType),
                Call("rangeFactorization", futureLaw)), Comma,
            RowBreak, Grp(),
            jointLaw, Colon, Sp, Call("Product", pastType,
                Call("Product", stateType, futureType)), Sp, To, Sp, real,
            Sp, Colon, Eq, Sp, Seq(LambdaLower, Sp, triple, Comma, Sp,
                Call("ite", Seq(Apply(stateMap, past), Eq, state),
                    Seq(Call("toReal", Apply(prior, past)), Sp, Cdot, Sp,
                        Call("toReal", Apply(Apply(futureLaw, past), future))), D(0))), Comma,
            RowBreak, Grp(),
            Forall, Sp, past, Colon, Sp, pastType, Comma, Sp,
            state, Colon, Sp, stateType, Comma, Sp,
            future, Colon, Sp, futureType, Comma,
            RowBreak, Grp(),
            Apply(jointLaw, triple), Sp, Cdot, Sp,
            Call("marginal", yFirst, state), Sp, Eq, Sp,
            Call("xyProjection", jointLaw, pastState), Sp, Cdot, Sp,
            Call("xzProjection", yFirst, stateFuture), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
