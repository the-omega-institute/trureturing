using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class InvolutionDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A transformation descends through a surjective readout exactly when it preserves "
            + "readout fibers.",
        H("Involution Descent"),
        Blocks(Describe.Lean(
            DescribeId.Create("kernel-stability-characterizes-descent"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/ObservationTopology/InvolutionDescent."
                    + "kernelStable_iff_exists_descended"),
            H("Kernel stability is exactly existence of a descended map"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "KernelStable says that source points with equal readout values remain "
                        + "equal after transforming and reading out again.")),
                Paragraph(Text(
                    "For a surjective readout, a chosen representative of each coordinate "
                        + "defines a coordinate transformation. Kernel stability makes that "
                        + "definition independent of the representative.")),
                Paragraph(Text(
                    "Conversely, any factorization through a coordinate map carries equal "
                        + "readout values to equal transformed readout values.")),
                Paragraph(Text(
                    "The equivalence is conditional on surjectivity; existence through an "
                        + "arbitrary nonsurjective readout is not claimed."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coordinate = F.Id("Coordinate");
        Formula readout = F.Id("readout");
        Formula transform = F.Id("transform");
        Formula descended = F.Id("descended");
        Formula factorization = Seq(
            descended, Sp, Circ, Sp, readout, Sp, Eq, Sp,
            readout, Sp, Circ, Sp, transform);
        Formula conclusion = Seq(
            Call("KernelStable", readout, transform), Sp, Iff, Sp,
            Exists, Sp, descended, Colon, Sp, Arrow(coordinate, coordinate),
            Comma, Sp, factorization);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, readout, Colon, Sp, Call("Concept", state, coordinate),
            Comma, Sp,
            transform, Colon, Sp, Arrow(state, state), Comma, RowBreak, Grp(),
            Call("Surjective", readout), Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
