using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class LosslessReadoutReflexiveGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lossless readout realizes every Boolean state predicate but no same-state catalog is exhaustive.",
        H("Lossless Readout Reflexive Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observable-pullback"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap."
                        + "observablePullback"),
                H("Observable predicate pullback"),
                StatementSource.FromAuthor(PullbackFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A Boolean predicate on the realized range of R is pulled back along the "
                        + "canonical realized readout from states to that range."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lossless-readout-predicate-equiv"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap."
                        + "lossless_readout_predicate_equiv"),
                H("A lossless readout realizes every state predicate uniquely"),
                StatementSource.FromAuthor(PredicateEquivFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary types A and O and an injective readout R from A to O, "
                            + "pullback is a bijection from Boolean predicates on range R to "
                            + "all Boolean predicates on A.")),
                    Paragraph(Text(
                        "The proof uses the exact identification with Mathlib's range "
                            + "factorization and its predicate-space composition theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("observable-diagonal-escape"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap."
                        + "observable_diagonal_escape"),
                H("The transported diagonal escapes every same-state catalog"),
                StatementSource.FromAuthor(DiagonalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Given the same arbitrary carriers and injective readout, every catalog "
                            + "from states to Boolean predicates on range R misses a predicate q.")),
                    Paragraph(Text(
                        "At each state a, q disagrees with catalog a at the realized readout of "
                            + "a, making the witness explicit on the empirical image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lossless-observation-strict-reflexive-gap"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap."
                        + "lossless_observation_strict_reflexive_gap"),
                H("Empirical predicate completeness with strict reflexive failure"),
                StatementSource.FromAuthor(StrictGapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An injective readout simultaneously gives a bijective predicate "
                            + "pullback and makes every same-state catalog non-surjective onto "
                            + "the observable Boolean predicate space.")),
                    Paragraph(Text(
                        "The result does not claim a new diagonal theorem; it identifies the "
                            + "escaped predicate space with the image of the verified readout."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Range(Formula readout) => Call("range", readout);

    private static Formula PredicateType(Formula readout) =>
        Arrow(Range(readout), F.Id("Bool"));

    private static Formula CatalogType(Formula states, Formula readout) =>
        Arrow(states, PredicateType(readout));

    private static Formula CarrierPremises(Formula states, Formula observations, Formula readout) =>
        F.Seq(states, F.Colon, F.Sp, F.Id("Type"), F.Comma, F.Sp,
            observations, F.Colon, F.Sp, F.Id("Type"), F.Comma, F.Sp,
            readout, F.Colon, F.Sp, Arrow(states, observations));

    private static Formula PullbackFormula()
    {
        Formula states = F.Id("A");
        Formula observations = F.Id("O");
        Formula readout = F.Id("R");
        Formula predicate = F.Id("q");
        Formula state = F.Id("a");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, CarrierPremises(states, observations, readout), F.Comma,
            F.RowBreak, F.Grp(), predicate, F.Colon, F.Sp, PredicateType(readout), F.Comma, F.Sp,
            state, F.Colon, F.Sp, states, F.Comma, F.RowBreak, F.Grp(),
            Call("observablePullback", readout, predicate, state), F.Sp, F.Eq, F.Sp,
            Call("q", Call("realizedReadout", readout, state)), F.Dot));
    }

    private static Formula PredicateEquivFormula()
    {
        Formula states = F.Id("A");
        Formula observations = F.Id("O");
        Formula readout = F.Id("R");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, CarrierPremises(states, observations, readout), F.Comma,
            F.RowBreak, F.Grp(), Call("Injective", readout), F.Sp, F.Rightarrow, F.Sp,
            Call("Bijective", Call("observablePullback", readout)), F.Dot));
    }

    private static Formula DiagonalFormula()
    {
        Formula states = F.Id("A");
        Formula observations = F.Id("O");
        Formula readout = F.Id("R");
        Formula catalog = F.Id("catalog");
        Formula predicate = F.Id("q");
        Formula state = F.Id("a");
        Formula realized = Call("realizedReadout", readout, state);
        return F.Disp(F.Seq(
            F.Forall, F.Sp, CarrierPremises(states, observations, readout), F.Comma,
            F.RowBreak, F.Grp(), Call("Injective", readout), F.Comma, F.Sp,
            catalog, F.Colon, F.Sp, CatalogType(states, readout), F.Comma,
            F.RowBreak, F.Grp(), F.Exists, F.Sp, predicate, F.Colon, F.Sp,
            PredicateType(readout), F.Comma, F.Sp, F.Forall, F.Sp,
            state, F.Colon, F.Sp, states, F.Comma, F.Sp,
            Call("q", realized), F.Sp, F.Neq, F.Sp,
            Call("catalog", state, realized), F.Dot));
    }

    private static Formula StrictGapFormula()
    {
        Formula states = F.Id("A");
        Formula observations = F.Id("O");
        Formula readout = F.Id("R");
        Formula catalog = F.Id("catalog");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, CarrierPremises(states, observations, readout), F.Comma,
            F.RowBreak, F.Grp(), Call("Injective", readout), F.Sp, F.Rightarrow,
            F.RowBreak, F.Grp(), Call("Bijective", Call("observablePullback", readout)),
            F.Sp, F.Land, F.RowBreak, F.Grp(), F.Forall, F.Sp, catalog, F.Colon, F.Sp,
            CatalogType(states, readout), F.Comma, F.Sp, F.Neg, F.Sp,
            Call("Surjective", catalog), F.Dot));
    }
}
