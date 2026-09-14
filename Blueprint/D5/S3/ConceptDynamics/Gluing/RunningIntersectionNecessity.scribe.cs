using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class RunningIntersectionNecessityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-node path with scopes {x}, {y}, {x} has matching edge images and no global row.",
        H("Running Intersection Necessity"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-matching-claim"),
                DeclarationHandle.Create(Module + "EdgeMatchingSufficesWithoutRI"),
                H("The assertion of sufficiency without RI"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("T"), Comma, Sp, F.Id("S"), Comma, Sp, F.Id("Gamma"),
                    Comma, Sp, Call("IsTree", F.Id("T")), Sp, Land, Sp,
                    Call("NonemptyLocalRelations", F.Id("Gamma")), Sp, Land, Sp,
                    Call("EdgeProjectionConsistency", F.Id("T"), F.Id("S"), F.Id("Gamma")),
                    Sp, To, Sp, Call("Nonempty", F.Id("J"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The closed assertion quantifies over graphs on Fin 3, scopes in Fin 2, "
                        + "and local relations of dependent assignments with constant value type "
                        + "Fin 2. It says that a tree with nonempty local relations and equal "
                        + "complete edge projection images has a nonempty raw global join."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-path-refutation"),
                DeclarationHandle.Create(Module + "edge_matching_without_ri_is_false"),
                H("A single variable receives contradictory values"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("EdgeMatchingSufficesWithoutRI")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the path 0-1-2, variables x = 0 and y = 1, and scopes {x}, {y}, "
                            + "{x}. The three relations are singletons containing the rows x = 0, "
                            + "y = 0, and x = 1. Each relation is nonempty. Both edge separators "
                            + "are empty, so both complete projection images are the singleton "
                            + "empty assignment.")),
                    Paragraph(Text(
                        "A global row would restrict to x = 0 at node 0 and x = 1 at node 2. "
                            + "These evaluate the same global coordinate, contradicting 0 unequal "
                            + "to 1 in Fin 2. The x occurrences are disconnected. Consequently "
                            + "complete edge consistency is insufficient without RI."))),
                DescribeRole.Theorem))));
}
