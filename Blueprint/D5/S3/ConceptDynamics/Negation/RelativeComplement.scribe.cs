using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Negation;

internal sealed class RelativeComplementDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Negation/RelativeComplement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative complement is universe-indexed; pullbacks preserve it, images may fail.",
        H("Relative Complement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pullback-preserves-relative-complement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "preimage_relativeComplement"),
                H("Pullback preserves relative complement"),
                StatementSource.FromAuthor(PullbackFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any readout, pulling back the complement of a subset inside a "
                            + "chosen ambient region equals the complement of the pulled-back "
                            + "subset inside the pulled-back ambient region.")),
                    Paragraph(Text(
                        "The equality is definitional: inverse image preserves both membership "
                            + "in the ambient set and exclusion from the subset without any "
                            + "injectivity or surjectivity assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("direct-image-can-fail-to-preserve-complement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "image_complement_counterexample"),
                H("Direct image can fail to preserve complement"),
                StatementSource.FromAuthor(ImageCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The counterexample uses first projection from a Boolean pair and the "
                            + "singleton containing the all-false pair. Its complement still "
                            + "contains a point whose first coordinate is false.")),
                    Paragraph(Text(
                        "Consequently false belongs to the image of the complement, while it "
                            + "does not belong to the complement of the singleton image. Even "
                            + "this finite surjective map therefore fails to commute with direct "
                            + "image complementation."))),
                DescribeRole.Theorem))));

    private static Formula PullbackFormula()
    {
        Formula q = F.Id("q");
        Formula ambient = F.Id("U");
        Formula subset = F.Id("A");

        return Disp(Seq(
            Call("preimage", q, Call("relativeComplement", ambient, subset)),
            Sp, Eq, Sp,
            Call(
                "relativeComplement",
                Call("preimage", q, ambient),
                Call("preimage", q, subset)),
            Dot));
    }

    private static Formula ImageCounterexampleFormula()
    {
        Formula projection = F.Id("fst");
        Formula falseValue = F.Id("false");
        Formula point = Call("pair", falseValue, falseValue);
        Formula singleton = Call("singleton", point);

        return Disp(Seq(
            Call("image", projection, Call("complement", singleton)),
            Sp, Neq, Sp,
            Call("complement", Call("image", projection, singleton)),
            Dot));
    }
}
