using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class OriginalFiniteResolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalFiniteResolution", H("Finite symbolic resolution of functional expressions"), Blocks(
            Describe.Lean(DescribeId.Create("finite-symbolic-resolution"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFiniteResolution.original_finite_resolution"),
                H("Syntactic finite derivations and values forced in every solution"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("This expression language has finite grounds, named finite or divergent parameter atoms, decorated state variables and ordered pairs. It has no independent literal Omega constructor. Undefined states may have arbitrary completed values. The compiler uses exactly as many rounds as there are original states; parameter atoms remain symbolic and are never expanded to a bounded family of values.")),
                    Paragraph(Text("Successful compilation is equivalent to a finite syntactic derivation from the defining expressions. A compiled finite expression evaluates to the same finite native tree in every solution at every parameter assignment. Repeated names, atomic coincidences, arbitrary powers and zero state or parameter counts are allowed. Stabilization follows because every nonstationary round adds a previously unresolved state.")),
                    Paragraph(Text("The conclusion does not construct a solution or identify semantic finiteness of a canonical solution. Literal Omega in the larger native source language is handled by a separate exact encoding with a fixed divergent internal slot, followed by decoding to the original finite parameter names. No external literature novelty is asserted."))
                ), DescribeRole.Theorem)
        )));
}
