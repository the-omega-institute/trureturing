using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class MinimalPredictiveCompletionQuotientDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximal forward congruence inside the readout kernel yields the coarsest "
            + "quotient that preserves both the current readout and the state update.",
        H("Minimal Predictive Completion Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-readout-relation-is-an-equivalence"),
                DeclarationHandle.Create(DeclarationPrefix + "readout_relation_equivalence"),
                H("The readout relation is an equivalence"),
                StatementSource.FromAuthor(ReadoutRelationEquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The readout relation identifies two states exactly when their current "
                            + "observations agree. Reflexivity, symmetry, and transitivity are "
                            + "therefore inherited directly from equality in the observation "
                            + "space.")),
                    Paragraph(Text(
                        "No state is chosen in this argument, so the equivalence law remains "
                            + "valid when the state type is empty. This supplies the setoid "
                            + "structure needed to form the predictive quotient."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("the-predictive-quotient-is-the-coarsest-completion"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "minimal_predictive_completion_quotient"),
                H("The predictive quotient is the coarsest completion"),
                StatementSource.FromAuthor(MinimalPredictiveCompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The predictive setoid uses the largest forward congruence contained "
                            + "in the kernel of the current readout. Its quotient projection "
                            + "therefore forgets only distinctions that are observationally "
                            + "invisible now and remain compatible with one update step.")),
                    Paragraph(Text(
                        "Containment in the readout kernel makes the readout descend to the "
                            + "quotient, while forward congruence makes the state update descend. "
                            + "The two displayed factorization equations say respectively that "
                            + "the quotient preserves the present observation and carries the "
                            + "dynamics.")),
                    Paragraph(Text(
                        "Every other setoid that is a forward congruence and lies inside the "
                            + "readout kernel is contained in this maximal congruence. Hence the "
                            + "predictive projection factors through that setoid's quotient "
                            + "projection. With Refines(coarse, fine) meaning that the coarse "
                            + "readout factors through the fine one, this is precisely the stated "
                            + "coarseness direction.")),
                    Paragraph(Text(
                        "The construction assumes neither finiteness nor inhabitedness. Empty "
                            + "state spaces, singleton observation spaces, identity updates, and "
                            + "constant readouts are therefore covered without separate cases."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula ReadoutRelationEquivalenceFormula()
    {
        Formula state = F.Id("X");
        Formula observationType = F.Id("O");
        Formula readout = F.Id("q");
        Formula relation = Call("readoutRelation", readout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, observationType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(readout, Arrow(state, observationType)), Comma, RowBreak, Grp(),
            Call("Equivalence", relation), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula MinimalPredictiveCompletionFormula()
    {
        Formula state = F.Id("X");
        Formula observationType = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula quotientReadout = F.Id("qbar");
        Formula quotientUpdate = F.Id("Fbar");
        Formula setoid = F.Id("S");
        Formula quotient = Call("PredictiveQuotient", update, readout);
        Formula projection = Call("predictiveProjection", update, readout);
        Formula setoidRelation = Call("setoidRelation", setoid);
        Formula readoutPreservation = Seq(
            readout, Sp, Eq, Sp,
            quotientReadout, Sp, Circ, Sp, projection);
        Formula dynamicsDescent = Seq(
            projection, Sp, Circ, Sp, update, Sp, Eq, Sp,
            quotientUpdate, Sp, Circ, Sp, projection);
        Formula coarseness = Seq(
            Forall, Sp, Typed(setoid, Call("Setoid", state)), Comma, RowBreak, Grp(),
            Call("TauCongruence", update, setoidRelation), Sp, Rightarrow,
            RowBreak, Grp(),
            setoidRelation, Sp, Subseteq, Sp, Call("readoutRelation", readout),
            Sp, Rightarrow, RowBreak, Grp(),
            Call("Refines", projection, Call("QuotientMk", setoid)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, observationType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(readout, Arrow(state, observationType)), Comma, RowBreak, Grp(),
            Exists, Sp,
            Typed(quotientReadout, Arrow(quotient, observationType)), Comma, Sp,
            Typed(quotientUpdate, Arrow(quotient, quotient)), Comma, RowBreak, Grp(),
            readoutPreservation, Sp, Land, RowBreak, Grp(),
            dynamicsDescent, Sp, Land, RowBreak, Grp(),
            Open, coarseness, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
