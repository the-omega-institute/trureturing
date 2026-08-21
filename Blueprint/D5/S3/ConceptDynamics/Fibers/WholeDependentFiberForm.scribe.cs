using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class WholeDependentFiberFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A whole type is canonically equivalent to the dependent sum of the fibers of any coordinate readout.",
        H("Whole Dependent Fiber Form"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("whole-dependent-fiber-form"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Fibers/WholeDependentFiberForm."
                        + "whole_dependent_fiber_form"),
                H("Whole dependent fiber form"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary coordinate readout q : X -> B, the residual fiber "
                            + "over b consists of an object x together with an equality q(x) = b.")),
                    Paragraph(Text(
                        "The equivalence sends each object to its coordinate and reflexive fiber "
                            + "witness, and recovers an object by forgetting those coordinates.")),
                    Paragraph(Text(
                        "The statement quantifies over arbitrary types and an arbitrary readout. "
                            + "It requires no quotient object, surjectivity, section, linear "
                            + "structure, or metric, and its Lean axiom audit has no choice dependency.")),
                    Paragraph(Text(
                        "The canonical Concept and ConceptFiber vocabulary is imported from the "
                            + "existing concept-fiber family, whose exact decomposition theorem is "
                            + "applied directly."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula coordinate = F.Id("b");
        Formula readout = F.Id("q");
        Formula fiber = F.Id("R");
        Formula sigma = Seq(Sum, Sp, Underscore,
            Grp(coordinate, Colon, Sp, coordinateType), Sp,
            Apply(fiber, coordinate));

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coordinateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            readout, Colon, Sp, source, Sp, To, Sp, coordinateType, Comma, Esc,
            Operatorname, Grp(F.Id("Nonempty")), Open,
            source, Sp, Equiv, Sp, sigma, Close, Dot));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
