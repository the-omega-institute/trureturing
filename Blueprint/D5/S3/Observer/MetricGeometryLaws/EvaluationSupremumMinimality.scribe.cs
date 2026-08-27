using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class EvaluationSupremumMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Evaluation suprema are the least pseudometrics dominating every readout distance.",
        H("Evaluation Supremum Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("evaluation-suprema-are-least-dominating"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometryLaws/EvaluationSupremumMinimality."
                        + "evaluation_suprema_are_least_dominating"),
                H("State and protocol evaluation suprema are least dominating"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Lambda is a pseudometric law carrier, e evaluates a state-protocol "
                            + "pair, and delta_X and delta_P are arbitrary competitor "
                            + "pseudometrics on the exact source carriers.")),
                    Paragraph(Text(
                        "The two displayed suprema are the canonical source constructions. "
                            + "Any pointwise upper bound for every state readout bounds the "
                            + "state supremum, and the same least-upper-bound argument applies "
                            + "to protocol responses.")),
                    Paragraph(Text(
                        "The surrounding bounded-law assumption is not needed for this stronger "
                            + "minimality statement: each competitor hypothesis already supplies "
                            + "the required upper bound."))),
                DescribeRole.Theorem))));

    private static Formula Type() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) content.AddRange([Comma, Sp]);
            content.Add(arguments[index]);
        }

        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Supremum(Formula index, Formula carrier, Formula body) =>
        Seq(
            Operatorname, Grp(F.Id("sup")),
            Underscore, Grp(index, Sp, InMacro, Sp, carrier), Sp,
            body);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula protocol = F.Id("P");
        Formula law = Lambda;
        Formula evaluation = F.Id("e");
        Formula stateMetric = Seq(DeltaLower, Underscore, Grp(state));
        Formula protocolMetric = Seq(DeltaLower, Underscore, Grp(protocol));
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula outputDistance = new Formula.Subscript(F.Id("d"), law);
        Formula stateOutputDistance = Call(
            "dist",
            outputDistance,
            Call("eval", evaluation, x, p),
            Call("eval", evaluation, y, p));
        Formula protocolOutputDistance = Call(
            "dist",
            outputDistance,
            Call("eval", evaluation, x, p),
            Call("eval", evaluation, x, q));
        Formula statePremise = Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, state, Comma, Sp,
            Forall, Sp, p, Sp, InMacro, Sp, protocol, Comma, Esc,
            stateOutputDistance, Sp, Leq, Sp, Call("dist", stateMetric, x, y));
        Formula stateConclusion = Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, state, Comma, Esc,
            Supremum(p, protocol, stateOutputDistance), Sp, Leq, Sp,
            Call("dist", stateMetric, x, y));
        Formula protocolPremise = Seq(
            Forall, Sp, p, Comma, Sp, q, Sp, InMacro, Sp, protocol, Comma, Sp,
            Forall, Sp, x, Sp, InMacro, Sp, state, Comma, Esc,
            protocolOutputDistance, Sp, Leq, Sp, Call("dist", protocolMetric, p, q));
        Formula protocolConclusion = Seq(
            Forall, Sp, p, Comma, Sp, q, Sp, InMacro, Sp, protocol, Comma, Esc,
            Supremum(x, state, protocolOutputDistance), Sp, Leq, Sp,
            Call("dist", protocolMetric, p, q));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, protocol, Comma, Sp, law,
            Colon, Sp, Type(), Comma,
            RowBreak, Grp(),
            Call("PseudoMetricSpace", law), Comma, Sp,
            evaluation, Colon, Sp,
            new Formula.TypeArrow(state, new Formula.TypeArrow(protocol, law)), Comma,
            RowBreak, Grp(),
            stateMetric, Colon, Sp, Call("PseudoMetricSpace", state), Comma, Sp,
            protocolMetric, Colon, Sp, Call("PseudoMetricSpace", protocol), Comma,
            RowBreak, Grp(),
            Open, Open, statePremise, Close, Sp, Rightarrow, Sp, stateConclusion, Close,
            RowBreak, Grp(),
            Land,
            RowBreak, Grp(),
            Open, Open, protocolPremise, Close, Sp, Rightarrow, Sp, protocolConclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
