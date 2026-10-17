using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class CoherentFollowerCoverDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/CoherentFollowerCover.CoherentFollower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent closed forward-invariant finite-follower languages have finite live covers with onto maps on entire paths.",
        H("Coherent All-Subface Follower Covers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coherent-follower-0"),
                DeclarationHandle.Create(Owner + "finite_followers_of_graph"),
                H("Finite followers of a finite graph"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary alphabet and a finite vertex type, the nonempty followers of the complete graph language form a finite type. Consuming a finite past tracks the reachable subset at the next time. Every initial vertex is allowed, so the empty past begins at the entire vertex set and needs no predecessor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-1"),
                DeclarationHandle.Create(Owner + "followers_card_le_pow"),
                H("The powerset bound"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A presentation on n vertices has at most 2^n nonempty followers. Followers factor through reachable subsets, including subsets containing transient or dead vertices; no trimming premise is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-2"),
                DeclarationHandle.Create(Owner + "finite_followers_of_sofic"),
                H("Soficity supplies finite followers"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing IsSofic predicate supplies a finite vertex-labelled graph presentation and hence finite followers. No particular presentation is retained in the language-family data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-3"),
                DeclarationHandle.Create(Owner + "LanguageSystem"),
                H("Coherent language premises"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary index type I and a family of topological alphabets A_i, every finite scope F has a nonempty closed forward-invariant language L_F with finitely many nonempty followers. For F contained in G, the coordinate restriction of entire words in L_G has image exactly L_F. The shift need not be onto. ofSofic obtains this data from a coherent family of sofic languages. Finite alphabets are required only for finiteness of vertices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherent-follower-4"),
                DeclarationHandle.Create(Owner + "LanguageSystem.Context"),
                H("Reachable all-subface contexts"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write Q_H(u) for the follower of a finite past u in L_H. A context at F is the vector of Q_H(u restricted to H) over every H contained in F, realized by one common past u that extends to a word in L_F. Reachability is part of the definition; arbitrary independent choices of followers are excluded. The face type is finite by the powerset of F, even when I is uncountable. Contexts inject into the product of the finite follower types."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherent-follower-5"),
                DeclarationHandle.Create(Owner + "LanguageSystem.Vertex"),
                H("Allowed current letters"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A vertex consists of a reachable context s and a current letter a whose left derivative in the top component is nonempty. Its label is a. An edge requires the next context to be the componentwise derivative by the restrictions of a. The next letter is already allowed because its endpoint is a vertex. This gives deterministic context updates without choosing a representative past."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherent-follower-6"),
                DeclarationHandle.Create(Owner + "LanguageSystem.path_in_initial_follower"),
                H("Exact soundness from an arbitrary initial past"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let p be any entire graph path and let u represent its initial context. Then u concatenated with the whole label word of p belongs to L_F. The past u may be nonempty. At time n the edge equations reconstruct the context after u followed by the first n labels. All these finite prefixes have continuations. Choosing continuations gives a sequence eventually equal to the prescribed future in each coordinate; the existing product-convergence and closed-limit lemmas place that future in the closed initial follower."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-7"),
                DeclarationHandle.Create(Owner + "LanguageSystem.graphLanguage_exact"),
                H("The complete graph language is exact"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The graph language equals L_F with every initial vertex allowed. Forward invariance removes the initial finite past from path soundness. Conversely each word in L_F gives a path of its prefix contexts from the empty past. The construction uses one-sided time and requires no negative-time orbit or onto shift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-8"),
                DeclarationHandle.Create(Owner + "LanguageSystem.vertex_live"),
                H("Every vertex starts a whole path"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a finite past representing the vertex context and a whole continuation witnessing allowedness of its current letter. The prefix-context path of that single admitted concatenation, beginning after the chosen past, starts at the prescribed vertex. Thus no admitted vertex is dead."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-9"),
                DeclarationHandle.Create(Owner + "LanguageSystem.vertex_nonempty"),
                H("Every stage is nonempty"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A word from the nonempty language gives a prefix-context path and therefore an initial vertex. This remains valid for an empty coordinate scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-10"),
                DeclarationHandle.Create(Owner + "LanguageSystem.restrictVertex_label"),
                H("Labels commute with deletion"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vertex map restricts the current symbol and deletes the face-vector components outside the smaller scope. Its label is exactly the coordinate restriction of the original label."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-11"),
                DeclarationHandle.Create(Owner + "LanguageSystem.restrictVertex_edge"),
                H("Deletion preserves edges"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each smaller-scope face is also a larger-scope face. The corresponding derivative equation is literally one of the original edge equations. A projected allowed letter remains allowed by restriction of the common admitted extension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-12"),
                DeclarationHandle.Create(Owner + "LanguageSystem.restrictVertex_refl"),
                H("Identity on vertices"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restriction from a scope to itself is the identity, including the entire reachable context and its current letter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-13"),
                DeclarationHandle.Create(Owner + "LanguageSystem.restrictVertex_comp"),
                H("Exact vertex deletion squares"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F contained in G contained in H, restricting from H to G and then to F equals restriction directly from H to F. All subface components and symbols coincide; no choice of presentation or representative past enters the maps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-14"),
                DeclarationHandle.Create(Owner + "LanguageSystem.restrictPath_refl"),
                H("Identity on whole paths"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pointwise identity on vertices induces identity on entire path spaces."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-15"),
                DeclarationHandle.Create(Owner + "LanguageSystem.restrictPath_comp"),
                H("Exact whole-path deletion squares"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pointwise composition of vertex restrictions proves composition on complete infinite paths. Equality includes time zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-16"),
                DeclarationHandle.Create(Owner + "LanguageSystem.restrictPath_surjective"),
                H("Every prescribed whole path lifts"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix an arbitrary target path p, its label word z, and one past u representing its initial context. Initial-follower soundness puts the single concatenation uz in L_F. Whole-word coordinate surjectivity gives one w in L_G restricting to uz. At time n choose the context after the first length(u)+n letters of w and the current letter at that time. The resulting graph path restricts to p at every time: its context projects to the context after u followed by the first n letters of z, and its letter projects to z(n). The fine initial context is after a finite past and is not required to be empty. Vertex, edge or label surjectivity alone is not used as a replacement for this assertion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-17"),
                DeclarationHandle.Create(Owner + "LanguageSystem.projected_path_language"),
                H("Whole-path equality in the graph-language interface"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The label map here is the vertex restriction itself. Its complete graph language is exactly the smaller graph path language with identity labels. Edge preservation gives one inclusion; surjectivity of the entire path map gives the other."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-18"),
                DeclarationHandle.Create(Owner + "LanguageSystem.every_prefix_lifts"),
                H("Compatibility with the existing prefix criterion"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite alphabets, every finite prefix of every whole target path lifts through the vertex restriction. This applies the existing graphLanguage_eq_iff_prefix_lifts theorem to the exact whole-path equality. Its finite inverse-system compactness argument is reused rather than reproved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-19"),
                DeclarationHandle.Create(Owner + "LanguageSystem.vertex_card_bound_product"),
                H("One fixed finite product bound"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vertex cardinal is at most the alphabet cardinal times the product of the nonempty-follower cardinals over all subfaces H of F. The injection records the current symbol and all follower components; Nat.card product and Pi formulas supply the estimate. This bound depends only on the once-fixed languages at subfaces of F, independently of every later upper scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-20"),
                DeclarationHandle.Create(Owner + "LanguageSystem.empty_singleton_loop"),
                H("The empty-scope singleton loop"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At the empty scope the alphabet and whole-word type are singletons. Nonemptiness forces its language to contain the unique word, all reachable follower components are the full set, and its unique vertex has a loop."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coherent-follower-21"),
                DeclarationHandle.Create(Owner + "LanguageSystem.coherent_follower_cover"),
                H("Coherent finite live covers"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed graph stages are finite, nonempty, forward-live and exact presentations of their languages. The vertex and whole-path restrictions have identity and composition laws, preserve labels and edges, and are surjective on whole paths. The all-subface product bound and empty-scope loop describe the size and initial object. These conclusions are conditional on the coherent language family. A coherent family has not been constructed from an arbitrary compact source with shadowing, so original Peng Q5.1 remains open. The result is a general symbolic and topological dynamics bridge and carries no global novelty or official-resolution claim."))),
                DescribeRole.Theorem))));
}
