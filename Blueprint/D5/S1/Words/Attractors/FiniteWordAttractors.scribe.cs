using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Attractors;

internal sealed class FiniteWordAttractorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Attractors/FiniteWordAttractors.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/gheeraertromanastipulanti2023attractors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unrestricted attractors of finite words have attained minima and admit bounded factor transport.",
        H("Finite-word attractors and factor transport"),
        Blocks(
            Paragraph(Text("Attractors range over all subsets of positions in the same finite word. The source definition and letter lower-bound principle are distinguished from the formal infimum implementation and generic occurrence-transport proofs.")),
            Def("IsAttractor", "Unrestricted original positions", "For every type α, list w : List α and finite set S of natural positions, IsAttractor w S means both: S is a subset of range(w.length); and for every pair of naturals a,l with 0 < l and a+l ≤ w.length, there exist naturals b,p such that b+l ≤ w.length, p belongs to S, b ≤ p < b+l, and (w.drop a).take l equals (w.drop b).take l. Both occurrences are wholly inside this same finite word. Every finite position subset is eligible; there is no prescribed shape for S. This is the unnumbered string-attractor definition at the opening of Section 4. The paper uses positions 1 through w.length; its position equals the Lean position plus one, preserving factor equality, interval intersection and cardinality.", AssessedProvenance.FromLiterature(Source)),
            Def("gamma", "Attained minimum over all subsets", "For every type α and list w : List α, gamma w is the natural-number infimum sInf of the set of n for which there exists a finite set S of natural positions with IsAttractor w S and S.card=n. This noncomputable definition uses every such S. The natural infimum convention returns zero if the set is empty; attractor_minimum proves that this set is nonempty and the infimum is attained. Section 4 defines the minimum attractor size; the natural infimum presentation and its attainment proof are formalized here.", AssessedProvenance.FromRepo(Source)),
            Proof("attractor_minimum", "Unrestricted attained minimum", "For every type α with a DecidableEq dictionary and every list w : List α, all three conclusions hold: there exists a finite set S with IsAttractor w S and S.card=gamma w; every finite set S satisfying IsAttractor w S has gamma w ≤ S.card; and the cardinality of w.toFinset, the set of distinct letters in w, is at most gamma w. The statement includes the empty word. The full position set gives existence; singleton factors make selected positions cover the distinct letters. Section 4 and Example 19 supply the distinct-letter lower-bound principle. The three-clause finite-word infimum and singleton-coverage proof are formalized here as a necessary supplier of the full result.", AssessedProvenance.FromRepo(Source)),
            Proof("attractor_window_transfer", "Actual-window factor transport", "For every type α, list w : List α, naturals N,q,p,B and finite set S of natural positions, assume 0 < N, N ≤ w.length, 0 < q, q ≤ p, p ≤ N, q ≤ B and B ≤ N-1. Assume (w.drop (p-q)).take B = w.take B and p-q+B ≤ w.length. Assume IsAttractor (w.take (N-1)) S and q-1 belongs to S. Assume either B=N-1 or B belongs to S.erase(q-1). Finally assume either p=N and List.HasPeriod w N, or w.drop p is a prefix of w.take B. Then insert(p-1, S.erase(q-1)) is an attractor of the same entire word w, and its cardinality is at most S.card. All differences are natural subtraction; the window and occurrence bounds are part of the hypotheses. Theorem 23 contains a related concrete suffix-window argument. This proved generic law allows arbitrary words and selected sets with either of the two displayed occurrence-reduction modes.", AssessedProvenance.FromRepo(Source)),
            Proof("periodic_attractor_extension", "Periodic endpoint extension", "For every type α, list w : List α, natural N and finite set S of natural positions, assume 0 < N, N ≤ w.length, List.HasPeriod w N and IsAttractor (w.take (N-1)) S. Then IsAttractor w (insert (N-1) S). Every valid nonempty factor is moved within the same word: reduction modulo N either crosses the added position or allows transfer from the old interior. Proposition 21 and the initial extension step of Theorem 23 supply the related periodic-extension principle. This generic finite-word formulation starts from the N-1 interior and is proved here.", AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Def(string name, string title, string prose, AssessedProvenance provenance) =>
        Node(name, title, prose, DescribeRole.Definition, provenance);
    private static DocumentBlock Proof(string name, string title, string prose, AssessedProvenance provenance) =>
        Node(name, title, prose, DescribeRole.Theorem, provenance);
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);

}
