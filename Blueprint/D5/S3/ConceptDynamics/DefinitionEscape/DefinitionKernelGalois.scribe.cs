using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class DefinitionKernelGaloisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Family kernels form a Galois connection detecting primitive and productive escape.",
        H("Definition Kernel Galois"),
        Blocks(Describe.Lean(
            DescribeId.Create("definition-relation-galois"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois.definition_relation_galois"),
            H("Definition families and relations form a Galois connection"),
            StatementSource.FromAuthor(Formula()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The theorem reuses the canonical RelationInvariantReadouts and jointKernel carriers. A family is invariant on a relation exactly when the relation is contained in the common kernel of every family member.")),
                Paragraph(Text("The two implications unpack the same pairwise equality in opposite directions. No auxiliary kernel or replacement readout is introduced."))),
            DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula gamma = F.Id("Gamma");
        Formula relation = F.Id("relation");
        return Disp(Seq(
            Call("Subset", gamma, Call("RelationInvariantReadouts", relation)),
            Sp, Iff, Sp,
            Call("Subset", relation,
                Call("jointKernel", Call("definitionReadout", gamma))), Dot));
    }
}
