using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class DualSupremumPseudometricKernelsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The state-row and protocol-column evaluation suprema are pseudometrics with the "
            + "exact extensional kernels.",
        H("Double-Extensional Supremum Pseudometrics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("state-observation-supremum-distance"),
                DeclarationHandle.Create(Prefix + "stateObservationDistance"),
                H("State distance is the protocol supremum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two states, stateObservationDistance is the supremum over every "
                        + "protocol of the law-carrier distance between their evaluations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("protocol-response-supremum-distance"),
                DeclarationHandle.Create(Prefix + "protocolResponseDistance"),
                H("Protocol distance is the state supremum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two protocols, protocolResponseDistance is the supremum over every "
                        + "state of the law-carrier distance between their evaluations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("double-extensional-supremum-pseudometrics"),
                DeclarationHandle.Create(
                    Prefix + "dual_supremum_pseudometric_kernels"),
                H("Both supremum distances have the exact evaluation kernels"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The shared law carrier is a metric space whose distances are bounded "
                            + "by one. Pointwise nonnegativity, symmetry, and the triangle law "
                            + "pass to each bounded real supremum.")),
                    Paragraph(Text(
                        "The proof treats empty state and protocol types separately, so no "
                            + "unstated inhabitation or finiteness premise is added.")),
                    Paragraph(Text(
                        "A supremum is zero exactly when every contributing metric distance "
                            + "is zero. Metric separation then identifies the zero-distance "
                            + "relations with equality of evaluation rows and columns, making "
                            + "the exact double-extensional quotients precisely the two "
                            + "zero-distance quotients."))),
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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula StateDistance(Formula evaluation, Formula first, Formula second) =>
        Apply(F.Id("stateObservationDistance"), evaluation, first, second);

    private static Formula ProtocolDistance(
        Formula evaluation, Formula first, Formula second) =>
        Apply(F.Id("protocolResponseDistance"), evaluation, first, second);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("State");
        Formula protocolType = F.Id("Protocol");
        Formula lawType = F.Id("Law");
        Formula evaluation = F.Id("e");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula a = F.Id("a");
        Formula b = F.Id("b");

        Formula stateLaws = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp, z, InMacro, Sp, stateType,
            Comma, RowBreak, Grp(),
            D(0), Sp, Leq, Sp, StateDistance(evaluation, x, y), Sp, Land, Sp,
            StateDistance(evaluation, x, x), Sp, Eq, Sp, D(0), Sp, Land,
            RowBreak, Grp(),
            StateDistance(evaluation, x, y), Sp, Eq, Sp,
            StateDistance(evaluation, y, x), Sp, Land, RowBreak, Grp(),
            StateDistance(evaluation, x, y), Sp, Leq, Sp,
            StateDistance(evaluation, x, z), Sp, Plus, Sp,
            StateDistance(evaluation, z, y));
        Formula protocolLaws = Seq(
            Forall, Sp, p, Comma, Sp, q, Comma, Sp, r, InMacro, Sp, protocolType,
            Comma, RowBreak, Grp(),
            D(0), Sp, Leq, Sp, ProtocolDistance(evaluation, p, q), Sp, Land, Sp,
            ProtocolDistance(evaluation, p, p), Sp, Eq, Sp, D(0), Sp, Land,
            RowBreak, Grp(),
            ProtocolDistance(evaluation, p, q), Sp, Eq, Sp,
            ProtocolDistance(evaluation, q, p), Sp, Land, RowBreak, Grp(),
            ProtocolDistance(evaluation, p, q), Sp, Leq, Sp,
            ProtocolDistance(evaluation, p, r), Sp, Plus, Sp,
            ProtocolDistance(evaluation, r, q));
        Formula stateKernel = Seq(
            Forall, Sp, x, Comma, Sp, y, InMacro, Sp, stateType, Comma, Sp,
            StateDistance(evaluation, x, y), Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            Open, Forall, Sp, p, InMacro, Sp, protocolType, Comma, Sp,
            Apply(evaluation, x, p), Sp, Eq, Sp, Apply(evaluation, y, p), Close);
        Formula protocolKernel = Seq(
            Forall, Sp, p, Comma, Sp, q, InMacro, Sp, protocolType, Comma, Sp,
            ProtocolDistance(evaluation, p, q), Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            Open, Forall, Sp, x, InMacro, Sp, stateType, Comma, Sp,
            Apply(evaluation, x, p), Sp, Eq, Sp, Apply(evaluation, x, q), Close);
        Formula bound = Seq(
            Forall, Sp, a, Comma, Sp, b, InMacro, Sp, lawType, Comma, Sp,
            Call("dist", a, b), Sp, Leq, Sp, D(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, protocolType, Comma, Sp, lawType,
            Colon, Sp, F.Id("Type"), Comma, RowBreak, Grp(),
            Typed(evaluation, Arrow(stateType, Arrow(protocolType, lawType))), Comma,
            RowBreak, Grp(),
            Call("MetricSpace", lawType), Sp, Land, Sp, Open, bound, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, stateLaws, Close, Sp, Land, RowBreak, Grp(),
            Open, protocolLaws, Close, Sp, Land, RowBreak, Grp(),
            Open, stateKernel, Close, Sp, Land, RowBreak, Grp(),
            Open, protocolKernel, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
