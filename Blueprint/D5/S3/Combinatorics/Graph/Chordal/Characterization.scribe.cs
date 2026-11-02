using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class CharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source theorem ranges over V : Type u for any universe u; the existing native predicate ranges over V : Type 0. NativeChordal denotes FaalNonStable.Chordal. Later(G,ord,v) denotes exactly the set of u in V satisfying ord(v) < ord(u) and G.Adj v u. IsPEO has exactly the injective and isClique_later fields. Both finite equivalences include empty and disconnected graphs and require neither a supplied Fintype nor decidable adjacency.",
        H("Finite chordality and perfect elimination"),
        Blocks(
            Describe.Lean(DescribeId.Create("peo-converse"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/Characterization.isChordal"),
                H("An elimination order implies chordality"),
                StatementSource.FromAuthor(Disp(All("V", Call("Type", F.Id("u")), All("G", Call("SimpleGraph", F.Id("V")), Logic(Call("Finite", F.Id("V")), FormulaLogicOperator.Implies, All("ord", new Formula.TypeArrow(F.Id("V"), Call("Nat")), Logic(Call("IsPEO", F.Id("G"), F.Id("ord")), FormulaLogicOperator.Implies, Call("IsChordal", F.Id("G"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text("The Option-parent forest has clique bags. On a cycle of length at least four choose a vertex whose top bag has largest rank. Its two cycle neighbors belong to that bag and are distinct. Their adjacency is absent from the cycle edges, so it is a chord. Rotation retains the same cycle support and unordered edges."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-characterization"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/Characterization.isChordal_iff_exists_isPEO"),
                H("The complete source characterization"),
                StatementSource.FromAuthor(Disp(All("V", Call("Type", F.Id("u")), All("G", Call("SimpleGraph", F.Id("V")), Logic(Call("Finite", F.Id("V")), FormulaLogicOperator.Implies, Logic(Call("IsChordal", F.Id("G")), FormulaLogicOperator.Iff, Some("ord", new Formula.TypeArrow(F.Id("V"), Call("Nat")), Call("IsPEO", F.Id("G"), F.Id("ord"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text("Dirac elimination supplies the forward implication; the deepest-top bag argument supplies the converse. The natural-number ranking is not required to be a contiguous enumeration. This is the classical known characterization with the original source construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-correspondence"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/Characterization.native_chordal_iff_isChordal"),
                H("Positional and off-cycle-edge chordality"),
                StatementSource.FromAuthor(Disp(All("V", Call("Type", D(0)), All("G", Call("SimpleGraph", F.Id("V")), Logic(Call("NativeChordal", F.Id("G")), FormulaLogicOperator.Iff, Call("IsChordal", F.Id("G"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text("Each conversion uses the given cycle. Positions are strictly below its length. A supported occurrence at the closing endpoint is normalized to zero. The unordered edge may have either orientation. Absence from the edge list rules out consecutive positions and the last-to-first pair, and these positional exclusions conversely imply absence from the same edge list. This correspondence needs no finiteness hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-characterization"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/Characterization.chordal_iff_exists_order"),
                H("The exact native finite characterization"),
                StatementSource.FromAuthor(Disp(All("V", Call("Type", D(0)), All("G", Call("SimpleGraph", F.Id("V")), Logic(Call("Finite", F.Id("V")), FormulaLogicOperator.Implies, Logic(Call("NativeChordal", F.Id("G")), FormulaLogicOperator.Iff, Some("ord", new Formula.TypeArrow(F.Id("V"), Call("Nat")), Logic(Call("Injective", F.Id("ord")), FormulaLogicOperator.And, All("v", F.Id("V"), Call("IsClique", F.Id("G"), Call("Later", F.Id("G"), F.Id("ord"), F.Id("v")))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text("The native correspondence and the full source equivalence give precisely an injective natural-number ranking and clique later-neighborhoods. The two fields are unpacked directly. No connectivity, nonemptiness, Fintype, decidability or preselected simplicial vertex is added."))),
                DescribeRole.Theorem))));


    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Logic(Formula l, FormulaLogicOperator op, Formula r) =>
        new Formula.Logic(l, op, r);
}
