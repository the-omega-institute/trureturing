using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class WeavingCoefficientConsumerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform coefficients of actual weaving states.",H("Uniform coefficients of actual weaving states"),Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Topology/WeavingCoefficientConsumer.two_reference_unsigned_error"),
                H("Uniform coefficients of actual weaving states"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least two and m at least three, transport each actual reference graph through the explicit interval-first vertex order. It is connected, has nm edges and forward degree at most four. The canonical signed coefficient estimate therefore applies to both varying graph families with the same constant. The proved graphStatePolynomial_eq_mixed reindexing transfers it to H, which is defined as the literal mixed-circle state polynomial. Set d=n modulo 2 and r=(n-d)/2, with bOne=(r+d)m-d and bZero=rm+d. For every k at least one, the absolute difference between the sum of the two coefficient magnitudes at degree k and choose(bOne+k-1,k)+choose(bZero+k-1,k) is at most 2 times uniformCoefficientConstant(4,k) times (nm+1) to the power k-1. The reverse triangle inequality removes the coefficient signs without assuming their eventual values."))),DescribeRole.Theorem),
            Paragraph(Text("The identification with the source Jones invariant remains a separate formal obligation. The ordinary route requires integral Hecke coset spanning, restriction of the trace to Z[q,q inverse,z], and a ring map before specialization. It then localizes at z and eta=1-q+z and adjoins u with u squared=q/(z eta), sending u to the compatible link root lambda. Specialization from the generic rational function field is insufficient. These ring and trace statements, closure normalization, coefficient endpoints and the final twist-number limit are not Lean conclusions of this module.")))));
}
