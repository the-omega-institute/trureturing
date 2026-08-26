using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InvolutionLogic;

internal sealed class InvolutionTransversalDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InvolutionLogic/InvolutionTransversal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Boolean orientation of a fixed-point-free involution is an orbit transversal.",
        H("Involution Transversal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transversal-law-is-preimage-complement"),
                DeclarationHandle.Create(Prefix + "orbitTransversal_iff_preimage_eq_compl"),
                H("The transversal law is a preimage-complement equation"),
                StatementSource.FromAuthor(PreimageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "OrbitTransversal requires the image of each point to lie in the set "
                            + "exactly when the point itself lies outside it.")),
                    Paragraph(Text(
                        "Extensionality turns this pointwise biconditional into equality of "
                            + "the set's preimage with its complement.")),
                    Paragraph(Text(
                        "This equivalence does not assume involutivity; it unfolds the named "
                            + "transversal predicate for the displayed transformation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("involution-sends-a-transversal-to-its-complement"),
                DeclarationHandle.Create(Prefix + "image_eq_compl_of_orbitTransversal"),
                H("An involution sends its transversal to the complement"),
                StatementSource.FromAuthor(ImageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the transformation is involutive and the set is an orbit "
                            + "transversal. A point selected by the set maps outside it.")),
                    Paragraph(Text(
                        "Conversely, every point outside the set is the image of its own "
                            + "transformed partner, which the transversal law places inside.")),
                    Paragraph(Text(
                        "Both hypotheses are retained in the antecedent; the image equality "
                            + "is not asserted for an arbitrary transformation or set."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Bindings(
        Formula carrier,
        Formula involution,
        Formula set) =>
        Seq(
            Forall, Sp, involution, Colon, Sp, Arrow(carrier, carrier), Comma, Sp,
            set, Colon, Sp, Call("Set", carrier), Comma, Sp);

    private static Formula PreimageFormula()
    {
        Formula carrier = F.Id("X");
        Formula involution = F.Id("iota");
        Formula set = F.Id("S");

        return Disp(Seq(
            Bindings(carrier, involution, set),
            Call("OrbitTransversal", involution, set), Sp, Iff, Sp,
            Call("preimage", involution, set), Sp, Eq, Sp,
            Call("complement", set), Dot));
    }

    private static Formula ImageFormula()
    {
        Formula carrier = F.Id("X");
        Formula involution = F.Id("iota");
        Formula set = F.Id("S");
        Formula hypotheses = Seq(
            Call("Involutive", involution), Sp, Land, Sp,
            Call("OrbitTransversal", involution, set));

        return Disp(Seq(
            Bindings(carrier, involution, set),
            Open, hypotheses, Close, Sp, Rightarrow, Sp,
            Call("image", involution, set), Sp, Eq, Sp,
            Call("complement", set), Dot));
    }
}
