using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class CompleteObservationExpressibilityCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementFactorization/"
            + "CompleteObservationExpressibilityCriterion."
            + "complete_observation_expressibility_tfae";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A target is expressible from the complete observation exactly when it is constant on every joint fiber.",
        H("Complete Observation Expressibility Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-observation-expressibility-criterion"),
                DeclarationHandle.Create(Declaration),
                H("Expressibility, kernel inclusion, and fiber constancy agree"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The indexed observations are assembled by the canonical dependent "
                            + "joint readout and normalized to their realized image.")),
                    Paragraph(Text(
                        "The displayed theorem retains all three source clauses: effective-image "
                            + "factorization, equality-kernel inclusion, and the componentwise "
                            + "fiber implication.")),
                    Paragraph(Text(
                        "The reverse implication constructs the factor only on realized profiles "
                            + "using the pinned range splitting operation, so no values are chosen "
                            + "for unrealized profiles."))),
                DescribeRole.Theorem))));

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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("I");
        Formula state = F.Id("X");
        Formula values = F.Id("V");
        Formula targetType = F.Id("Y");
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        Formula i = F.Id("i");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula valueFamily = Seq(index, Sp, To, Sp, type);
        Formula readoutFamily = Seq(
            Forall, Sp, i, Colon, Sp, index, Comma, Sp,
            state, Sp, To, Sp, Apply(values, i));
        Formula profile = Call("jointReadout", readout);
        Formula expressible = Call(
            "Refines", target, Call("effectiveReadout", profile));
        Formula kernel = Seq(
            Call("ker", profile), Sp, Subseteq, Sp, Call("ker", target));
        Formula sameComponents = Seq(
            Forall, Sp, i, Colon, Sp, index, Comma, Sp,
            Apply(Apply(readout, i), x), Sp, Eq, Sp,
            Apply(Apply(readout, i), y));
        Formula fiberClause = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            Open, sameComponents, Close, Sp, Rightarrow, Sp,
            Apply(target, x), Sp, Eq, Sp, Apply(target, y));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, index, Comma, Sp, state, Comma, Sp,
            targetType, Colon, Sp, type, Comma, RowBreak, Grp(),
            values, Colon, Sp, valueFamily, Comma, Sp,
            readout, Colon, Sp, readoutFamily, Comma, RowBreak, Grp(),
            target, Colon, Sp, state, Sp, To, Sp, targetType, Comma,
            RowBreak, Grp(),
            Call("ListTFAE", Grp(OpenBracket,
                expressible, Comma, Sp, kernel, Comma, Sp, fiberClause,
                CloseBracket)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
