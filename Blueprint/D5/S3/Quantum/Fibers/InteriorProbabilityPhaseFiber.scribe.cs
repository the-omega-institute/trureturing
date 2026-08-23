using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class InteriorProbabilityPhaseFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strictly positive projective probability fiber has canonical relative phases.",
        H("Interior Probability Fibers and Relative Phases"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interior-probability-fiber-relative-phase-coordinates"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/InteriorProbabilityPhaseFiber."
                        + "interior_probability_fiber_relative_phase_coordinates_bijective"),
                H("Relative phases coordinatize the interior probability fiber"),
                StatementSource.FromAuthor(FiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An interior probability vector has n plus one strictly positive real "
                            + "coordinates summing to one. A polar representative pairs those "
                            + "probabilities with one unit complex phase per basis coordinate.")),
                    Paragraph(Text(
                        "Projective states are constructed by quotienting representatives that "
                            + "have equal probabilities and differ by one common unit phase. The "
                            + "basis-probability map forgets the phase class.")),
                    Paragraph(Text(
                        "The named coordinate map divides each non-reference phase by phase zero. "
                            + "It is invariant under common phase, and gauge fixing phase zero to "
                            + "one supplies its inverse. Thus the fiber is coordinatized by exactly "
                            + "n independent circle factors."))),
                DescribeRole.Theorem))));

    private static Formula FiberFormula()
    {
        Formula n = F.Id("n");
        Formula index = F.Id("i");
        Formula probability = F.Id("p");
        Formula probabilityAt = Seq(probability, Underscore, Grp(index));
        Formula simplex = Seq(Delta, Underscore, Grp(n));
        Formula basis = F.Id("B");
        Formula map = Seq(F.Id("q"), Underscore, Grp(basis));
        Formula fiber = Seq(
            map, Caret, Grp(Minus, D(1)), OpenBrace, probability, CloseBrace);
        Formula relative = Call("relativePhaseCoordinates", probability);
        Formula torus = new Formula.Power(F.Id("T"), Grp(n));

        return Disp(Seq(
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            probability, InMacro, Sp, Operatorname, Grp(F.Id("int")), Open,
            simplex, Close, Comma, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp, probabilityAt, Sp, Gt, Sp, D(0), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("Bijective")), Open,
            relative, Colon, Sp, fiber, Sp, To, Sp, torus, Close, Dot));
    }
}
