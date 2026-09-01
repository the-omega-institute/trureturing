using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ObservationFormalConceptAdapterDocument : IScribeDocumentDefinition
{
    private const string Declaration = "D5/S3/ConceptDynamics/ObservationFormalConceptAdapter.extentClosure_singleton_eq_jointKernel_class";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Readout kernels are singleton extent closures in Mathlib formal concept "
            + "analysis.",
        H("Observation Kernels as Formal-Concept Extents"),
        Blocks(Describe.Lean(
            DescribeId.Create("observation-formal-concept-adapter"),
            DeclarationHandle.Create(Declaration),
            H("A singleton extent closure is the common-kernel class"),
            StatementSource.FromAuthor(ExtentFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "An attribute is a pair consisting of one readout in the family and one output value. A state has that attribute exactly when the readout returns that value.")),
                Paragraph(Text(
                    "Closing a singleton under Mathlib's polar Galois connection therefore retains exactly the states agreeing with the original state under every readout.")),
                Paragraph(Text(
                    "The resulting set is equal to the repository joint-kernel equivalence class and hence supplies a direct adapter into the upstream complete concept lattice."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois")),
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

    private static Formula ExtentFormula()
    {
        Formula family = F.Id("Gamma");
        Formula state = F.Id("s");
        Formula other = F.Id("y");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, family, Comma, Sp, state, Colon,
            RowBreak, Grp(),
            Call("extentClosure",
                Call("observationIncidence", family),
                Seq(OpenBrace, state, CloseBrace)),
            RowBreak, Grp(),
            Eq, Sp, OpenBrace, other, Sp, Mid, Sp,
            Open, state, Comma, Sp, other, Close, Sp, InMacro, Sp,
            Call("jointKernel", family), CloseBrace, Dot,
            End, Grp(F.Id("gathered"))));
    }

}
