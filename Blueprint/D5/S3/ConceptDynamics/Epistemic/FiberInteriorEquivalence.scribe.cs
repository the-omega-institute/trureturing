using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class FiberInteriorEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Epistemic/FiberInteriorEquivalence."
            + "fiber_interior_equivalence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interior truth in a readout partition topology is exactly truth on the "
            + "current readout fiber.",
        H("Fiber Interior Equivalence"),
        Blocks(Describe.Lean(
            DescribeId.Create("fiber-interior-equivalence"),
            DeclarationHandle.Create(Declaration),
            H("Fiber knowledge equivalence"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The topology is the canonical partition topology induced by the "
                        + "readout into a discrete coordinate space.")),
                Paragraph(Text(
                    "An interior set is open and therefore saturated along readout "
                        + "fibers. Membership at x consequently transfers to every y "
                        + "with the same readout before factivity gives membership in P.")),
                Paragraph(Text(
                    "Conversely, the readout fiber through x is open in the partition "
                        + "topology. If P holds throughout that fiber, the fiber is an "
                        + "open neighborhood of x contained in P, so x lies in the "
                        + "interior.")),
                Paragraph(Text(
                    "The module imports the existing partition topology and fiber "
                        + "knowledge primitives; repository and pinned-library searches "
                        + "found no exact theorem for their equivalence."))),
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

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateType = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula state = F.Id("x");
        Formula other = F.Id("y");
        Formula readout = F.Id("C");
        Formula predicate = F.Id("P");
        Formula partitionTopology = Apply(F.Id("partitionTopology"), readout);
        Formula interior = Apply(F.Id("interior"), partitionTopology, predicate);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, coordinateType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, Apply(F.Id("Concept"), stateType, coordinateType), Comma, Sp,
            predicate, Colon, Sp, Apply(F.Id("Set"), stateType), Comma, RowBreak, Grp(),
            state, Colon, Sp, stateType, Comma, RowBreak, Grp(),
            state, Sp, InMacro, Sp, interior,
            Sp, Iff, Sp,
            Forall, Sp, other, Colon, Sp, stateType, Comma, Sp,
            Apply(readout, other), Sp, Eq, Sp, Apply(readout, state),
            Sp, Rightarrow, Sp, other, Sp, InMacro, Sp, predicate, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
