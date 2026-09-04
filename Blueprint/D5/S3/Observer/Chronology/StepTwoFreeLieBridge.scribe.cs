using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepTwoFreeLieBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/StepTwoFreeLieBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor Magnus brackets map to represented commutators and free Lie brackets.",
        H("Step-Two Free Lie and Representation Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tensor-multiplication"),
                DeclarationHandle.Create(Prefix + "tensorMultiplication"),
                H("Tensor multiplication representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's multiplication map sends a tensor pair to its product in the "
                        + "chosen associative algebra."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signature-representation"),
                DeclarationHandle.Create(Prefix + "representTensorSignature"),
                H("Represented tensor signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Degree one is retained and the genuine degree-two tensor is multiplied "
                        + "inside the target algebra."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("free-lie-evaluation"),
                DeclarationHandle.Create(Prefix + "freeLieEvaluation"),
                H("Free Lie evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's universal property extends event values uniquely to a Lie "
                        + "homomorphism into the associative algebra with commutator bracket."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("agreement"),
                DeclarationHandle.Create(
                    Prefix + "tensor_and_free_lie_brackets_agree"),
                H("Tensor and free-Lie agreement"),
                StatementSource.FromAuthor(AgreementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The representation of a single-event signature is its truncated exponential, the representation is multiplicative for Chen composition, and it is compatible with every chronological word signature; the universal tensor bracket maps to the ring commutator, so the primitive Magnus coordinate represents to the step-two Magnus logarithm, with two events giving exactly the represented commutator.")),
                    Paragraph(Text(
                        "The bracket of two free generators evaluates to the commutator of their observed values, so the tensor and free-Lie realizations agree under every associative-algebra representation."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/PrimitiveMagnusLog")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/StepTwoChronologicalSignature")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula AgreementFormula() => Disp(Seq(
        Call("mul",
            Call("tensorCommutator", Call("f", F.Id("a")), Call("f", F.Id("b")))),
        Sp, Eq, Sp,
        Call("freeLieEval", F.Id("f"),
            Call("bracket",
                Call("of", F.Id("a")), Call("of", F.Id("b")))), Dot));
}
