using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class PullbackAlgebraFiberAtomsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraFiberAtoms."
            + "nonzero_pullback_atoms_are_effective_fibers";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimal nonempty events in the canonical pullback algebra are realized fibers.",
        H("Atoms of the Pullback Algebra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonzero-pullback-atoms-are-effective-fibers"),
                DeclarationHandle.Create(Declaration),
                H("Nonzero pullback atoms are exactly the realized fibers"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The pullback algebra is the repository's canonical family of "
                            + "proposition-valued events that factor through the readout.")),
                    Paragraph(Text(
                        "The left side states nonemptiness, pullback observability, and "
                            + "minimality against every nonempty observable subevent. The "
                            + "right side identifies the event with one fiber over a realized "
                            + "readout value.")),
                    Paragraph(Text(
                        "A point in a nonempty minimal event selects its fiber. Fiber "
                            + "constancy puts that fiber inside the event, and minimality "
                            + "forces equality. Conversely, any nonempty observable subevent "
                            + "of a fiber contains the whole fiber.")),
                    Paragraph(Text(
                        "No finiteness assumption is used: the characterization holds for "
                            + "arbitrary state and readout carriers, and therefore includes "
                            + "the finite-carrier corollary."))),
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
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("O");
        Formula readout = F.Id("q");
        Formula eventSet = F.Id("A");
        Formula candidate = F.Id("C");
        Formula observed = F.Id("o");
        Formula state = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula events = Call("Set", stateType);
        Formula algebra = Call("PullbackAlgebra", readout);
        Formula candidateConditions = Seq(
            Call("Nonempty", candidate), Sp, Land, Sp,
            candidate, Sp, InMacro, Sp, algebra, Sp, Land, Sp,
            candidate, Sp, Subseteq, Sp, eventSet, Sp, Rightarrow, Sp,
            eventSet, Sp, Subseteq, Sp, candidate);
        Formula minimalAtom = Seq(
            Call("Nonempty", eventSet), Sp, Land, Sp,
            eventSet, Sp, InMacro, Sp, algebra, Sp, Land, RowBreak, Grp(),
            Forall, Sp, candidate, Colon, Sp, events, Comma, Sp,
            candidateConditions);
        Formula fiber = Seq(
            OpenBrace, state, Colon, Sp, stateType, Sp, Mid, Sp,
            Apply(readout, state), Sp, Eq, Sp, Call("val", observed),
            CloseBrace);
        Formula realizedFiber = Seq(
            Exists, Sp, observed, Colon, Sp, Call("range", readout), Comma, Sp,
            eventSet, Sp, Eq, Sp, fiber);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, outputType, Colon, Sp, type,
            Comma, Sp, readout, Colon, Sp, stateType, Sp, To, Sp, outputType,
            Comma, RowBreak, Grp(),
            Forall, Sp, eventSet, Colon, Sp, events, Comma, RowBreak, Grp(),
            Open, minimalAtom, Close, Sp, Iff, RowBreak, Grp(),
            Open, realizedFiber, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
