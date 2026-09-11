using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Observation;

internal sealed class CoarsestObservationQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Observation/CoarsestObservationQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quotient by an observation kernel is the coarsest exact interface, and every "
            + "accurate surjective readout factors uniquely through it.",
        H("Coarsest Observation Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observation-quotient-recovers"),
                DeclarationHandle.Create(Prefix + "observation_quotient_recovers"),
                H("The canonical observation quotient recovers the observation uniquely"),
                StatementSource.FromAuthor(ObservationQuotientFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quotient identifies exactly those states with the same observation. "
                        + "The observation therefore descends to a unique decoder on the quotient, "
                        + "and composing that decoder with the canonical projection recovers the "
                        + "original observation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("accurate-surjective-readout-factors"),
                DeclarationHandle.Create(Prefix + "accurate_surjective_readout_factors"),
                H("Every accurate surjective readout factors uniquely through the quotient"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a surjective readout can decode the observation, its fibers are contained "
                        + "in observation fibers. A representative from each readout value then "
                        + "defines a map to the canonical quotient, and surjectivity makes that map "
                        + "both total and unique."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

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

    private static Formula ObservationQuotientFormula()
    {
        Formula stateType = F.Id("X");
        Formula observationType = F.Id("O");
        Formula observation = F.Id("observation");
        Formula decoder = F.Id("decoder");
        Formula quotient = Call("Quotient", Call("ker", observation));
        Formula projection = Apply(F.Id("observationProjection"), observation);
        Formula factorization = Seq(observation, Sp, Eq, Sp,
            Apply(decoder, projection));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, observationType), TypeUniverse()),
            Comma, Sp,
            Typed(observation, Arrow(stateType, observationType)), Comma, RowBreak, Grp(),
            Exists, Bang, Sp,
            Typed(decoder, Arrow(quotient, observationType)), Comma, Sp,
            factorization, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FactorizationFormula()
    {
        Formula stateType = F.Id("X");
        Formula observationType = F.Id("O");
        Formula readoutType = F.Id("Q");
        Formula observation = F.Id("observation");
        Formula readout = F.Id("readout");
        Formula decoder = F.Id("decoder");
        Formula factor = F.Id("factor");
        Formula quotient = Call("Quotient", Call("ker", observation));
        Formula projection = Apply(F.Id("observationProjection"), observation);
        Formula accurate = Seq(observation, Sp, Eq, Sp,
            Apply(decoder, readout));
        Formula conclusion = Seq(
            Exists, Bang, Sp,
            Typed(factor, Arrow(readoutType, quotient)), Comma, Sp,
            Seq(projection, Sp, Eq, Sp, Apply(factor, readout)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, observationType, Comma, Sp, readoutType),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(observation, Arrow(stateType, observationType)), Comma, Sp,
            Typed(readout, Arrow(stateType, readoutType)), Comma, RowBreak, Grp(),
            Call("Surjective", readout), Comma, Sp,
            Typed(decoder, Arrow(readoutType, observationType)), Comma, RowBreak, Grp(),
            accurate, Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
