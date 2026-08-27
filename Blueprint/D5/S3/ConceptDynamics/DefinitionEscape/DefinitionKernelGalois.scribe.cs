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
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("not-mem-semantic-closure-iff-kernel-witness"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois.not_mem_semanticClosure_iff_kernel_witness"),
            H("Escaping the semantic closure is exactly having a kernel witness"),
            StatementSource.FromAuthor(KernelWitnessFormula()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("A readout lies outside the semantic closure of a family exactly when some pair of points is identified by every member of the family yet separated by the readout.")),
                Paragraph(Text("Both directions reuse the fiber-constancy characterisation of the closure. No new kernel, separator, or replacement readout is introduced."))),
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

    private static Formula KernelWitnessFormula()
    {
        Formula state = F.Id("X");
        Formula inputOutput = F.Id("InputOutput");
        Formula output = F.Id("Output");
        Formula gamma = F.Id("Gamma");
        Formula target = F.Id("target");
        Formula left = F.Id("left");
        Formula right = F.Id("right");
        Formula definition = F.Id("definition");
        Formula outside = Seq(Neg, Open, target, Sp, InMacro, Sp,
            Call("SemanticClosure", gamma), Close);
        Formula fibersAgree = Seq(Forall, Sp, definition, Colon, Sp, gamma, Comma, Sp,
            Call("definition", left), Sp, Eq, Sp, Call("definition", right));
        Formula targetSeparates = Seq(
            Call("target", left), Sp, Neq, Sp, Call("target", right));
        Formula witness = Seq(Exists, Sp, left, Comma, Sp, right, Colon, Sp, state,
            Comma, Sp,
            Open, fibersAgree, Close, Sp, Land, Sp, targetSeparates);
        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, inputOutput, Comma, Sp, output,
            Colon, Sp, F.Id("Type"), Comma, Esc,
            gamma, Colon, Sp, Call("Set", Call("Concept", state, inputOutput)),
            Comma, Sp,
            target, Colon, Sp, Call("Concept", state, output), Comma, Esc,
            outside, Sp, Iff, Sp, witness, Dot));
    }
}
