using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class ControlQuotientUniversalMinimalityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality."
            + "control_quotient_universal_minimality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quotient by all monoid-indexed public outcomes is the universal coarsest "
            + "action-complete concept.",
        H("Control Quotient Universal Minimality"),
        Blocks(Describe.Lean(
            DescribeId.Create("control-quotient-is-the-universal-action-completion"),
            DeclarationHandle.Create(Declaration),
            H("The control quotient is the universal action completion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The control profile is constructed directly from the source monoid action: "
                        + "at a state it records the public readout after every action. The named "
                        + "control carrier is the quotient by equality of these complete profiles, "
                        + "and the canonical projection is retained in every public equation.")),
                Paragraph(Text(
                    "The empty action recovers the present readout. Multiplication in the monoid "
                        + "makes every action preserve profile equality, producing an induced "
                        + "action on the quotient; evaluating a profile at a chosen action gives "
                        + "the corresponding public consequence from the current quotient value.")),
                Paragraph(Text(
                    "For any competing concept, the theorem requires recovery, action closure, "
                        + "and consequence determination as separate public premises. Consequence "
                        + "determination forces its equality kernel into the control kernel, and "
                        + "the imported realized-image criterion supplies the unique factor onto "
                        + "the canonical quotient image.")),
                Paragraph(Text(
                    "Finally, finite intervention words and single monoid actions induce the same "
                        + "state equivalence. Word composition gives one direction, while the "
                        + "one-action word gives the reverse, identifying this quotient with the "
                        + "family's dynamic completion at the kernel level."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula monoid = F.Id("M");
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula action = F.Id("m");
        Formula point = F.Id("x");
        Formula profile = F.Id("Kctl");
        Formula quotient = F.Id("Zctl");
        Formula projection = F.Id("pi");
        Formula candidate = F.Id("C");
        Formula factor = F.Id("h");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula actionAtPoint = Seq(action, Sp, Cdot, Sp, point);
        Formula actionMap = Call("act", action);
        Formula profileDefinition = Seq(
            Apply(profile, point, action), Sp, Colon, Eq, Sp,
            Apply(readout, actionAtPoint));
        Formula quotientDefinition = Seq(
            quotient, Sp, Colon, Eq, Sp, Call("Quotient", Call("ker", profile)));
        Formula projectionDefinition = Seq(
            projection, Sp, Colon, Eq, Sp, Call("controlProjection", readout));
        Formula recovery = Seq(
            readout, Sp, Eq, Sp, Call("controlReadout", readout), Sp, Circ, Sp,
            projection);
        Formula actionClosure = Seq(
            Forall, Sp, action, Comma, Sp,
            projection, Sp, Circ, Sp, actionMap, Sp, Eq, Sp,
            Call("controlAction", readout, action), Sp, Circ, Sp, projection);
        Formula consequence = Seq(
            Forall, Sp, action, Comma, Sp,
            Call("outcome", readout, action), Sp, Eq, Sp,
            Call("controlOutcome", readout, action), Sp, Circ, Sp, projection);
        Formula candidateConditions = Seq(
            Call("Recoverable", readout, candidate), Sp, Land, Sp,
            Call("ActionClosed", candidate), Sp, Land, Sp,
            Call("OutcomeDetermined", readout, candidate));
        Formula uniqueFactor = Seq(
            Exists, Bang, Sp, factor, Colon, Sp,
            Call("range", candidate), Sp, To, Sp, Call("range", projection), Comma, Sp,
            Call("rangeFactorization", projection), Sp, Eq, Sp,
            factor, Sp, Circ, Sp, Call("rangeFactorization", candidate));
        Formula minimality = Seq(
            Forall, Sp, candidate, Comma, Sp,
            Open, candidateConditions, Close, Sp, Rightarrow, Sp,
            Open, uniqueFactor, Close);
        Formula dynamicIdentification = Seq(
            Call("ker", profile), Sp, Eq, Sp,
            Call("ker", Call("DynClosure", readout, Call("act", monoid))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, monoid, Comma, Sp, state, Comma, Sp, output,
            Colon, Sp, type, Comma, Sp,
            Call("MonoidAction", monoid, state), Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma,
            RowBreak, Grp(),
            profileDefinition, Comma, Sp, quotientDefinition, Comma,
            RowBreak, Grp(),
            projectionDefinition, Comma,
            RowBreak, Grp(),
            recovery, Sp, Land,
            RowBreak, Grp(),
            Open, actionClosure, Close, Sp, Land,
            RowBreak, Grp(),
            Open, consequence, Close, Sp, Land,
            RowBreak, Grp(),
            Open, minimality, Close, Sp, Land,
            RowBreak, Grp(),
            dynamicIdentification, Dot,
            End, Grp(F.Id("gathered"))));
    }

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
}
