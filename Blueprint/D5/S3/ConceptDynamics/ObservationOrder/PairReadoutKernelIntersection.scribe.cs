using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class PairReadoutKernelIntersectionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/PairReadoutKernelIntersection."
            + "pair_readout_kernel_eq_intersection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The kernel of a paired readout is the intersection of its two kernels.",
        H("Pair Readout Kernel Intersection"),
        Blocks(Describe.Lean(
            DescribeId.Create("paired-readout-kernel-is-the-component-intersection"),
            DeclarationHandle.Create(Declaration),
            H("A paired readout kernel is the component intersection"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The paired readout records the outputs of two ordinary readouts on the "
                        + "same source state.")),
                Paragraph(Text(
                    "Equality of pairs projects to equality in both coordinates. Conversely, "
                        + "the two component equalities reconstruct equality of the pair.")),
                Paragraph(Text(
                    "Thus joint indistinguishability is exactly the intersection of the two "
                        + "component indistinguishability relations."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula firstOutput = F.Id("Y");
        Formula secondOutput = F.Id("Z");
        Formula first = F.Id("q");
        Formula second = F.Id("r");
        Formula pairReadout = Call("pairReadout", first, second);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(source, Comma, Sp, firstOutput, Comma, Sp, secondOutput),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(first, Seq(source, Sp, To, Sp, firstOutput)), Comma, Sp,
            Typed(second, Seq(source, Sp, To, Sp, secondOutput)),
            Comma, RowBreak, Grp(),
            Call("K", pairReadout), Sp, Eq, Sp,
            Call("Intersection", Call("K", first), Call("K", second)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
