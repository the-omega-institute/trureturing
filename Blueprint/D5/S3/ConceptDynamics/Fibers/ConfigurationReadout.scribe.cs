using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;
internal sealed class ConfigurationReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual original-fibre composition and the unique static assignment from an empty reference.",
        H("Legal configuration readouts"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-path-composition"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/ConfigurationReadout.actual_path_composition_iff"),
                H("Two-edge diamonds characterize all legal path composites"),
                StatementSource.FromAuthor(Disp(All("E",Call("Type"),Instance(Call("PartialOrder",F.Id("E")),All("C",Call("Predicate",Call("Finset",F.Id("E"))),All("R",Call("LocalReadout",F.Id("C")),Rel(All("A",Call("FiniteConfigurations",F.Id("C")),All("B",Call("FiniteConfigurations",F.Id("C")),All("l",Call("List",F.Id("E")),All("m",Call("List",F.Id("E")),All("x",Call("Fibre",F.Id("R"),F.Id("A")),Rel(Conj(Call("Exec",F.Id("A"),F.Id("l"),F.Id("B")),Call("Exec",F.Id("A"),F.Id("m"),F.Id("B"))),Implies,Rel(Call("legalPathMap",F.Id("C"),F.Id("R"),F.Id("A"),F.Id("B"),F.Id("l"),F.Id("x")),Eq,Call("legalPathMap",F.Id("C"),F.Id("R"),F.Id("A"),F.Id("B"),F.Id("m"),F.Id("x"))))))))),Iff,Call("LegalDiamonds",F.Id("C"),F.Id("R"))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original readout has a fibre only at each finite legal configuration, and a map only at each actual basic edge. No state or edge map is postulated at an illegal configuration. Complete a legal fibre by Option of its proof-indexed original states; illegal vertices have only None. Each actual state embeds as Some. Along an execution with legal endpoints every intermediate lower set lies inside the legal final configuration and is legal. Thus a legal path remains Some, and its value determines a genuine endpoint-fibre map. Optional diamonds with illegal final endpoint end at None on both sides; those with legal final endpoint are exactly the supplied two-edge diamonds. The generic finite-endpoint connectivity theorem applies to this faithful completion. Injectivity of Some then gives equality of the original endpoint maps."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unique-static-assignment"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/ConfigurationReadout.static_assignment_unique"),
                H("The empty reference uniquely determines the compatible assignment"),
                StatementSource.FromAuthor(Disp(All("E",Call("Type"),Instance(Call("PartialOrder",F.Id("E")),All("C",Call("Predicate",Call("Finset",F.Id("E"))),All("R",Call("LocalReadout",F.Id("C")),Rel(Conj(Call("Apply",F.Id("C"),Emptyset),Call("LegalDiamonds",F.Id("C"),F.Id("R"))),Implies,All("x",Call("EmptyFibre",F.Id("C"),F.Id("R")),Unique("f",Call("SectionSpace",F.Id("R")),Conj(Rel(Call("Apply",F.Id("f"),Call("EmptyConfiguration",F.Id("C"))),Eq,F.Id("x")),Call("StaticCompatible",F.Id("C"),F.Id("R"),F.Id("f")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a legal path from the empty configuration to every finite configuration and transport the reference value along it. Diamond path independence makes the resulting value independent of that choice. Concatenating a chosen path with one actual basic edge proves compatibility with every supplied edge map. Conversely any compatible assignment propagates along every legal execution by induction, so its value at each configuration is the transported empty reference. This proves existence and uniqueness of the actual edge-compatible static assignment. Failure of a legal diamond prevents an unconditional removal of execution order."))),
                DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Unique(string name, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, Bang, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
    private static Formula Instance(Formula instance, Formula body) =>
        Seq(OpenBracket, instance, CloseBracket, Sp, body);
}
