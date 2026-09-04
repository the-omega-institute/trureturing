using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimitiveMagnusLogDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimitiveMagnusLog.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The step-two tensor logarithm is an antisymmetric primitive coordinate.",
        H("Primitive Step-Two Magnus Logarithm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tensor-commutator"),
                DeclarationHandle.Create(Prefix + "tensorCommutator"),
                H("Universal tensor commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The degree-two bracket is the difference of the two ordered pure "
                        + "tensors before any operator representation is selected."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("primitive-log"),
                DeclarationHandle.Create(Prefix + "doubledPrimitiveMagnus"),
                H("Doubled primitive Magnus coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtracting the tensor square of degree one from doubled degree two "
                        + "extracts the step-two logarithmic component."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("primitive-predicate"),
                DeclarationHandle.Create(Prefix + "IsPrimitiveDegreeTwo"),
                H("Degree-two primitive antisymmetry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A degree-two tensor is primitive in the truncated sense when the "
                        + "canonical factor flip negates it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("word-primitive"),
                DeclarationHandle.Create(
                    Prefix + "chronological_primitive_magnus"),
                H("Finite chronological logarithms are primitive"),
                StatementSource.FromAuthor(PrimitiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Tensor commutators are primitive, and a single-event logarithm has no degree-two part; the tensor BCH law adds the commutator of the degree-one coordinates under Chen multiplication, and concatenation therefore obeys the Chen-to-BCH append law, with two events giving exactly the tensor bracket and the swap negating it.")),
                    Paragraph(Text(
                        "For any step-two group-like signature the doubled Magnus coordinate is antisymmetric (primitive), so by the frozen Hopf balance every finite chronological logarithm is a primitive degree-two coordinate."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/TruncatedTensorHopf")),
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

    private static Formula PrimitiveFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("L"), Comma, Sp,
        Call("IsPrimitiveDegreeTwo",
            Call("doubledPrimitiveMagnus",
                Call("chronologicalTensorSignature", F.Id("f"), F.Id("L")))),
        Dot));
}
