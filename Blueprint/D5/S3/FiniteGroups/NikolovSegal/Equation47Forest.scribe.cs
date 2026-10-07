using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47ForestDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generator-labelled arc elimination solves all nonroot coordinates and leaves one ordered residual at each actual powered component root.",
        H("Directed forest reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-arc"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.Arc"),
                H("Arc"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A directed variable is a pair consisting of a generator index in Fin m and a source coordinate in I. Oppositely directed arcs remain separate variables, including when their endpoints coincide in reverse order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-incident"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.incident"),
                H("incident"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An arc is incident to its source and to the image of its source under its labelled permutation. A loop has the same two endpoints and is excluded from leaf elimination."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-vertex"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.vertex"),
                H("vertex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a group S, permutations tau and arbitrary component automorphisms alpha, the vertex word is the generator-ordered product of the inverse outgoing arc variable times the incoming arc variable transformed by its own component automorphism. No relation between opposite component automorphisms is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-actual-vertex"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.actual_vertex"),
                H("actual vertex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the actual factor coordinate law, with tau(j) equal to sigma(j) to the q power and alpha given by the q-step corrected component, the directed vertex word equals the corrected q-powered commutator coordinate. This is the exact equation (47) word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-vertex-update-bijective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.vertex_update_bijective"),
                H("vertex update bijective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix every arc except one nonloop arc incident to a vertex. As the remaining arc variable ranges over S, the vertex word is bijective. At the source it occurs inversely, and at the target its own automorphism applies; the surrounding products retain their order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-leaforder"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.LeafOrder"),
                H("LeafOrder"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every listed pair consists of a vertex and an incident nonloop arc. The pairwise condition says a later selected arc is not incident to an earlier listed vertex, so subsequent updates preserve equations already solved."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-solve"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.solve"),
                H("solve"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a nonloop arc incident to the specified vertex, choose the unique replacement value solving that vertex target by the update bijection. On other pairs the definition keeps the current value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-eliminate"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate"),
                H("eliminate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Process a leaf order recursively. At each listed pair, update exactly its selected arc to the value solving its target vertex. All other arc variables pass to the next step unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-eliminate-unused"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_unused"),
                H("eliminate unused"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An arc that is never selected by the elimination list retains its original value. This includes all unused labelled arcs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-eliminate-loop"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_loop"),
                H("eliminate loop"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a valid leaf order, every loop arc retains its original value because selected arcs are nonloops."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-eliminate-solves"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_solves"),
                H("eliminate solves"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a valid leaf order, the final eliminated assignment solves every listed vertex equation. The pairwise nonincidence condition ensures later replacements do not alter earlier equations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-eliminate-unique"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_unique"),
                H("eliminate unique"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a valid leaf order, any assignment agreeing with the initial assignment on unused arcs and solving all listed vertices equals the eliminated assignment. Induction uses uniqueness of each incident-arc replacement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-reconstruction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.reconstruction"),
                H("reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a valid leaf order and any initial assignment, an assignment preserving every unused arc and solving every vertex exists exactly when the eliminated assignment satisfies every vertex not listed. Both directions use the same initial unused-arc data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-exists-actual-leaforder"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.exists_actual_leafOrder"),
                H("exists actual leafOrder"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let I be finite and r select one root per actual q-powered component: r(v) is reachable from v and r is constant on reachability classes. Construct an acyclic spanning subgraph with the same reachability, together with a valid leaf order listing precisely vertices v different from r(v). Every selected variable is an actual generator-labelled arc belonging to the spanning forest. Sorting by decreasing distance permits mixed edge orientations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47forest-actual-forest-reconstruction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.actual_forest_reconstruction"),
                H("actual forest reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite coordinate type I, a group S, actual k, sigma and beta satisfying the coordinate law, a fixed correction tuple y and a root map r reachable from and constant on each actual q-powered component, there exists a leaf order listing exactly the nonroots. For every tuple target kappa and every initial arc assignment a, a corrected q-powered solution preserving all unused arcs exists if and only if the eliminated assignment solves the equation at each root v equal to r(v). Thus there is one exact ordered residual per powered component, including isolated vertices; original transitivity is not required."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Lemma 10.3 and equations (45)-(50), printed pages 228-231. The scalar PRODUCT premise is the input of Part II, Theorem 1.2, equivalent to Part I, Theorem 1.10; Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. These are adaptations and proofs of conditional consequences of published mathematics, with no originality claim. Uniform scalar existence, genuine type-II reconstruction, mixed representative bounds, uniform width, restricted Burnside bounds and unconditional strong completeness remain unproved.")))));
}
