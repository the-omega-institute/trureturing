using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class GlobalProfileQuotientUniversalityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The simultaneous-kernel quotient of a dependent family of readouts is the "
            + "coarsest interface that recovers every component, with finite-subfamily "
            + "recovery reduced to singleton tests and nonempty states shown necessary.",
        H("Global Profile Quotient Universality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("global-profile-relation-is-pointwise-agreement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "global_profile_relation_iff"),
                H("Global profile equivalence is pointwise agreement"),
                StatementSource.FromAuthor(GlobalProfileRelationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two states belong to the global profile relation exactly when every "
                            + "local readout gives them the same value. Equality of the dependent "
                            + "profiles yields each component equality, and the converse assembles "
                            + "those equalities into equality of the whole profile.")),
                    Paragraph(Text(
                        "The output type may vary with the index. The statement therefore compares "
                            + "the two readout values separately inside the appropriate output "
                            + "type at each index."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("every-local-readout-factors-through-the-global-profile"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "local_readouts_factor_through_global_profile"),
                H("Every local readout factors through the global profile quotient"),
                StatementSource.FromAuthor(LocalReadoutsFactorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each index, the corresponding local readout is constant on the "
                            + "simultaneous-kernel classes. It therefore descends to a readout on "
                            + "the global profile quotient, and composing that descended readout "
                            + "with the canonical projection recovers the original component.")),
                    Paragraph(Text(
                        "This recovery uses only the definition of the quotient relation. It needs "
                            + "neither an inhabited state space nor an inhabited index type."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("global-profile-quotient-universality"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "global_profile_quotient_universality"),
                H("The global profile quotient is the universal recovering interface"),
                StatementSource.FromAuthor(GlobalProfileUniversalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The canonical quotient projection recovers every member of the dependent "
                            + "readout family. Conversely, if an interface recovers every local "
                            + "readout, states in one of its fibers have identical global profiles, "
                            + "so the quotient projection factors through that interface.")),
                    Paragraph(Text(
                        "Thus the simultaneous-kernel quotient is coarsest among all interfaces "
                            + "that recover every component: any such interface retains enough "
                            + "information to determine the quotient class. Nonemptiness of the "
                            + "state space supplies a quotient value for interface points that are "
                            + "not represented by a state.")),
                    Paragraph(Text(
                        "It also suffices to require recovery for every finite indexed subfamily. "
                            + "Applying that hypothesis to the singleton index type recovers an "
                            + "arbitrary chosen component, after which the same universal "
                            + "factorization applies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-states-obstruct-unrestricted-factorization"),
                DeclarationHandle.Create(DeclarationPrefix + "empty_state_obstruction"),
                H("Empty states obstruct unrestricted factorization"),
                StatementSource.FromAuthor(EmptyStateObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take both the state type and the readout index type to be empty. Recovery "
                            + "of every local readout through the unique map to Unit is then "
                            + "vacuous because there are no local components.")),
                    Paragraph(Text(
                        "Nevertheless, the global quotient projection cannot factor through that "
                            + "map: such a factor would send the inhabited type Unit into the "
                            + "quotient of an empty state type, which has no element. This is the "
                            + "precise obstruction excluded by the main theorem's nonempty-state "
                            + "hypothesis."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula DependentReadoutType(
        Formula indexType,
        Formula stateType,
        Formula outputFamily,
        Formula index) =>
        Seq(
            Open, Typed(index, indexType), Close, Sp, To, Sp,
            stateType, Sp, To, Sp, Apply(outputFamily, index));

    private static Formula GlobalProfileRelationFormula()
    {
        Formula indexType = F.Id("P");
        Formula stateType = F.Id("X");
        Formula outputFamily = F.Id("O");
        Formula readouts = F.Id("q");
        Formula index = F.Id("p");
        Formula first = F.Id("x");
        Formula second = F.Id("y");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(indexType, Comma, Sp, stateType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(outputFamily, Arrow(indexType, TypeUniverse())), Comma, Sp,
            Typed(
                readouts,
                DependentReadoutType(indexType, stateType, outputFamily, index)),
            Comma, RowBreak, Grp(),
            Forall, Sp, Typed(Seq(first, Comma, Sp, second), stateType),
            Comma, RowBreak, Grp(),
            Open, first, Comma, Sp, second, Close, Sp, InMacro, Sp,
            Call("globalProfileRelation", readouts), Sp, Iff, Sp,
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Apply(readouts, index, first), Sp, Eq, Sp,
            Apply(readouts, index, second), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula LocalReadoutsFactorFormula()
    {
        Formula indexType = F.Id("P");
        Formula stateType = F.Id("X");
        Formula outputFamily = F.Id("O");
        Formula readouts = F.Id("q");
        Formula index = F.Id("p");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(indexType, Comma, Sp, stateType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(outputFamily, Arrow(indexType, TypeUniverse())), Comma, Sp,
            Typed(
                readouts,
                DependentReadoutType(indexType, stateType, outputFamily, index)),
            Comma, RowBreak, Grp(),
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call(
                "Refines",
                Apply(readouts, index),
                Call("globalProfileProjection", readouts)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula GlobalProfileUniversalityFormula()
    {
        Formula indexType = F.Id("P");
        Formula stateType = F.Id("X");
        Formula outputFamily = F.Id("O");
        Formula readouts = F.Id("q");
        Formula index = F.Id("p");
        Formula interfaceType = F.Id("R");
        Formula interfaceReadout = F.Id("r");
        Formula projection = Call("globalProfileProjection", readouts);
        Formula localRecovery = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call("Refines", Apply(readouts, index), projection));
        Formula recoversAll = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call("Refines", Apply(readouts, index), interfaceReadout));
        Formula universal = Seq(
            Forall, Sp, Typed(interfaceType, TypeUniverse()), Comma, Sp,
            Typed(interfaceReadout, Arrow(stateType, interfaceType)), Comma, RowBreak, Grp(),
            Open, recoversAll, Close, Sp, Rightarrow, Sp,
            Call("Refines", projection, interfaceReadout));
        Formula finiteUniversal = Seq(
            Forall, Sp, Typed(interfaceType, TypeUniverse()), Comma, Sp,
            Typed(interfaceReadout, Arrow(stateType, interfaceType)), Comma, RowBreak, Grp(),
            Call("RecoversFiniteSubfamilies", readouts, interfaceReadout),
            Sp, Rightarrow, Sp, Call("Refines", projection, interfaceReadout));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(indexType, Comma, Sp, stateType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(outputFamily, Arrow(indexType, TypeUniverse())), Comma, Sp,
            Typed(
                readouts,
                DependentReadoutType(indexType, stateType, outputFamily, index)),
            Comma, RowBreak, Grp(),
            Call("Nonempty", stateType), Sp, Rightarrow, RowBreak, Grp(),
            OpenBracket,
            Open, localRecovery, Close, Sp, Land, RowBreak, Grp(),
            Open, universal, Close, Sp, Land, RowBreak, Grp(),
            Open, finiteUniversal, Close,
            CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula EmptyStateObstructionFormula()
    {
        Formula empty = Emptyset;
        Formula unit = F.Id("Unit");
        Formula readouts = F.Id("q");
        Formula interfaceReadout = F.Id("r");
        Formula index = F.Id("p");
        Formula readoutType = Seq(
            Open, Typed(index, empty), Close, Sp, To, Sp,
            empty, Sp, To, Sp, unit);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Typed(readouts, readoutType), Comma, Sp,
            Typed(interfaceReadout, Arrow(empty, unit)), Comma, RowBreak, Grp(),
            OpenBracket,
            Open, Forall, Sp, Typed(index, empty), Comma, Sp,
            Call("Refines", Apply(readouts, index), interfaceReadout), Close,
            Sp, Land, RowBreak, Grp(),
            Neg, Sp,
            Call(
                "Refines",
                Call("globalProfileProjection", readouts),
                interfaceReadout),
            CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
