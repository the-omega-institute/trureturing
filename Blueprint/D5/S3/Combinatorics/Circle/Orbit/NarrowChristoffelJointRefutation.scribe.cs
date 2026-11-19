using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit;
internal sealed class NarrowChristoffelJointRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The primitive anchored numerator does not always admit a joint physical order",
        H("The complete physical assertion is refuted"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/NarrowChristoffelJointRefutation.result"),
                H("Failure at r=5,s=2,u=3"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The claim quantifies over every r>=2, 0<s<r, coprime(r,s), and 0<u<r with su=1 in ZMod r. It asks for one physical permutation sigma and a literal fresh cut at most r, with both complete OriginalOrder assertions at the explicit numerator and its double. The refutation retains that full claim, including the original all-natural prefix predicates. At r=5,s=2,u=3 the explicit numerator is 20. All 120 original physical permutations and all six literal cuts are covered by the finite obstruction; the native centered sources at (5,20) and (6,40) are used directly.")),
                    Paragraph(Text("The finite checks cover prefix lengths through 5 and 6. Any complete OriginalOrder would imply these finite checks, so their simultaneous impossibility refutes the original unbounded assertion. The proof expands Mathlib's original permutation recurrence and uses kernel decision reduction. It uses no native_decide, added axiom or copied narrow-orbit proof. NarrowDoublingOrbit retains its current arithmetic results. This finite refutation supplies no broader high-phase obstruction, complete Circle J result or official acceptance."))),
                DescribeRole.Theorem)), []));
}
