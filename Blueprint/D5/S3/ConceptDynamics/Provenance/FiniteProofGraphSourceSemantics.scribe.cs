using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Provenance;

internal sealed class FiniteProofGraphSourceSemanticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite acyclic source semantics is equivalent to a source-supported proof path.",
        H("Finite Proof-Graph Source Semantics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-semantic-iff-valid-source-path"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Provenance/FiniteProofGraphSourceSemantics."
                        + "source_semantic_iff_valid_source_path"),
                H("Source semantics is exactly valid source-path reachability"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite graph is represented on Fin n. Its edge relation carries a "
                            + "strictly increasing natural-number rank, which is a constructive "
                            + "certificate that no directed cycle can occur.")),
                    Paragraph(Text(
                        "A valid proof path is a nonempty finite list whose first vertex belongs "
                            + "to the available source set, whose adjacent vertices are graph "
                            + "edges, and whose final vertex is the requested conclusion.")),
                    Paragraph(Text(
                        "The proposition sourceSemantic graph sources target is the formal "
                            + "counterpart of the source's phi_c(S)=True condition. The theorem "
                            + "states exactly that this condition holds if and only if such a "
                            + "source-supported valid path exists.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no canonical directed "
                            + "proof-graph source-semantics carrier or theorem. The local "
                            + "definitions therefore record the source's finite graph and path "
                            + "semantics directly; the equivalence is definitional."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.AddRange([Comma, Sp]);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula graph = F.Id("graph");
        Formula sources = F.Id("sources");
        Formula target = F.Id("target");
        Formula path = F.Id("path");
        Formula fin = Apply(F.Id("Fin"), n);
        Formula graphType = Apply(F.Id("FiniteAcyclicProofGraph"), n);
        Formula sourceType = Apply(F.Id("Finset"), fin);
        Formula semantic = Apply(F.Id("sourceSemantic"), graph, sources, target);
        Formula pathType = Apply(F.Id("List"), fin);
        Formula validPath = Apply(
            F.Id("ValidProofPath"), graph, sources, target, path);
        Formula pathExists = Seq(
            Exists, Sp, path, Colon, Sp, pathType, Comma, Sp, validPath);

        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, graph, Colon, Sp, graphType, Comma, Sp,
            sources, Colon, Sp, sourceType, Comma, Sp, target, Colon, Sp, fin,
            Comma, RowBreak, Grp(),
            semantic, Sp, Iff, Sp, pathExists, Dot));
    }
}
