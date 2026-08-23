using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Factor;

internal sealed class FactorInvariantObservablesDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Factor/FactorInvariantObservables.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A readout admits factor dynamics exactly when pullback preserves every observable "
            + "that passes through it.",
        H("Factor-Invariant Observables"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factor-dynamics-transports-pulled-back-observables"),
                DeclarationHandle.Create(DeclarationPrefix + "factor_pullback_formula"),
                H("Factor dynamics transport pulled-back observables"),
                StatementSource.FromAuthor(FactorPullbackFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose the readout intertwines the state dynamics with a dynamics "
                            + "on the readout space. Pulling back any value-valued observable "
                            + "through the state dynamics then agrees with first transporting "
                            + "that observable by the factor dynamics and then reading out.")),
                    Paragraph(Text(
                        "Thus every observable obtained from the readout remains an observable "
                            + "of the same readout after one state update, with the transported "
                            + "observable given by composition with the factor dynamics."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("factor-dynamics-are-equivalent-to-observable-invariance"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "factor_iff_observable_invariance"),
                H("Factor dynamics are equivalent to observable invariance"),
                StatementSource.FromAuthor(FactorEquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A dynamics on the readout space makes the readout equivariant exactly "
                            + "when every observable through the readout remains expressible "
                            + "through that readout after pullback by the state dynamics.")),
                    Paragraph(Text(
                        "The forward direction transports each observable by composition with "
                            + "the factor dynamics. Conversely, applying invariance to the "
                            + "identity observable on the readout space produces the factor "
                            + "dynamics itself and its intertwining equation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("surjective-readouts-have-unique-factor-dynamics"),
                DeclarationHandle.Create(DeclarationPrefix + "factor_unique_of_surjective"),
                H("Surjective readouts have unique factor dynamics"),
                StatementSource.FromAuthor(FactorUniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If every readout value is represented by some state, two dynamics on "
                            + "the readout space that both intertwine the same state dynamics "
                            + "must agree everywhere.")),
                    Paragraph(Text(
                        "For any readout value, choose a state mapping to it. Both factor "
                            + "equations evaluate the two candidate dynamics there to the same "
                            + "updated readout, so surjectivity upgrades pointwise agreement on "
                            + "represented values to equality of the dynamics."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula Semiconjugacy(
        Formula readout, Formula stateDynamics, Formula factorDynamics) =>
        Seq(
            Compose(readout, stateDynamics), Sp, Eq, Sp,
            Compose(factorDynamics, readout));

    private static Formula FactorPullbackFormula()
    {
        Formula state = F.Id("Y");
        Formula readoutSpace = F.Id("Z");
        Formula valueSpace = F.Id("V");
        Formula readout = F.Id("phi");
        Formula stateDynamics = F.Id("tau");
        Formula factorDynamics = F.Id("sigma");
        Formula observable = F.Id("g");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(state, Comma, Sp, readoutSpace, Comma, Sp, valueSpace),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(readout, Arrow(state, readoutSpace)), Comma, Sp,
            Typed(stateDynamics, Arrow(state, state)), Comma, Sp,
            Typed(factorDynamics, Arrow(readoutSpace, readoutSpace)), Comma, RowBreak, Grp(),
            Semiconjugacy(readout, stateDynamics, factorDynamics), Sp,
            Rightarrow, Sp,
            Forall, Sp, Typed(observable, Arrow(readoutSpace, valueSpace)), Comma, RowBreak, Grp(),
            Compose(Compose(observable, readout), stateDynamics), Sp, Eq, Sp,
            Compose(Compose(observable, factorDynamics), readout), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FactorEquivalenceFormula()
    {
        Formula state = F.Id("Y");
        Formula readoutSpace = F.Id("Z");
        Formula valueSpace = F.Id("V");
        Formula readout = F.Id("phi");
        Formula stateDynamics = F.Id("tau");
        Formula factorDynamics = F.Id("sigma");
        Formula observable = F.Id("g");
        Formula transported = F.Id("h");

        Formula factorExists = Seq(
            Exists, Sp,
            Typed(factorDynamics, Arrow(readoutSpace, readoutSpace)), Comma, Sp,
            Semiconjugacy(readout, stateDynamics, factorDynamics));
        Formula invariant = Seq(
            Forall, Sp, Typed(valueSpace, TypeUniverse()), Comma, Sp,
            Forall, Sp, Typed(observable, Arrow(readoutSpace, valueSpace)), Comma, RowBreak, Grp(),
            Exists, Sp, Typed(transported, Arrow(readoutSpace, valueSpace)), Comma, Sp,
            Compose(Compose(observable, readout), stateDynamics), Sp, Eq, Sp,
            Compose(transported, readout));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, readoutSpace), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(readout, Arrow(state, readoutSpace)), Comma, Sp,
            Typed(stateDynamics, Arrow(state, state)), Comma, RowBreak, Grp(),
            Open, factorExists, Close, Sp, Iff, Sp,
            Open, invariant, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FactorUniquenessFormula()
    {
        Formula state = F.Id("Y");
        Formula readoutSpace = F.Id("Z");
        Formula readout = F.Id("phi");
        Formula stateDynamics = F.Id("tau");
        Formula firstDynamics = F.Id("sigma1");
        Formula secondDynamics = F.Id("sigma2");
        Formula stateValue = F.Id("y");
        Formula readoutValue = F.Id("z");

        Formula surjective = Seq(
            Forall, Sp, Typed(readoutValue, readoutSpace), Comma, Sp,
            Exists, Sp, Typed(stateValue, state), Comma, Sp,
            Apply(readout, stateValue), Sp, Eq, Sp, readoutValue);
        Formula bothFactors = Seq(
            Semiconjugacy(readout, stateDynamics, firstDynamics), Sp, Land, Sp,
            Semiconjugacy(readout, stateDynamics, secondDynamics));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, readoutSpace), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(readout, Arrow(state, readoutSpace)), Comma, Sp,
            Typed(stateDynamics, Arrow(state, state)), Comma, RowBreak, Grp(),
            Open, surjective, Close, Sp, Rightarrow, Sp,
            Forall, Sp,
            Typed(
                Seq(firstDynamics, Comma, Sp, secondDynamics),
                Arrow(readoutSpace, readoutSpace)),
            Comma, RowBreak, Grp(),
            Open, bothFactors, Close, Sp, Rightarrow, Sp,
            firstDynamics, Sp, Eq, Sp, secondDynamics, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
