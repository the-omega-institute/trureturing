using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ConceptFiberDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every concept readout decomposes its source into dependent fibers.",
        H("Concept Fiber Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("concept-readout"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ConceptFiberDecomposition.Concept"),
                H("A concept is a typed readout"),
                StatementSource.FromAuthor(ConceptFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary source and coordinate types X and B, a concept from X to B "
                        + "is exactly a function assigning one B-coordinate to each X-object."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("concept-fiber-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ConceptFiberDecomposition.concept_fiber_decomposition"),
                H("Concept fiber decomposition"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A concept is a readout q_C : X -> B_C. Its residual fiber over b is "
                            + "the dependent pair of x : X with a path q_C x = b.")),
                    Paragraph(Text(
                        "Mathlib's sigmaFiberEquiv supplies the explicit forward map sending x "
                            + "to q_C x with its canonical fiber witness and the backward map "
                            + "forgetting the coordinate. psigmaEquivSubtype and sigmaCongrRight "
                            + "transport that equivalence to the proof-relevant residual fiber "
                            + "notation used here."))),
                DescribeRole.Theorem))));

    private static Formula ConceptFormula()
    {
        Formula source = F.Id("X");
        Formula coordinate = F.Id("B");
        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coordinate, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Call("Concept", source, coordinate), Sp, Eq, Sp,
            new Formula.TypeArrow(source, coordinate), Dot));
    }

    private static Formula DecompositionFormula()
    {
        Formula source = F.Id("X");
        Formula coordinateType = Subscript(F.Id("B"), F.Id("C"));
        Formula coordinate = F.Id("b");
        Formula readout = Subscript(F.Id("q"), F.Id("C"));
        Formula fiber = Subscript(F.Id("R"), F.Id("C"));
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

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
