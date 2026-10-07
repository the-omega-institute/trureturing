using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FixedBlockRigidity;

internal sealed class BlockCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Arrow(Formula source, Formula target) =>
        F.Grp(F.Seq(source, F.To, F.Sp, target));
    private static Formula History(Formula graph) => Call("History", graph);
    private static Formula Graph(Formula edge) => Call("DirectedMultigraph", Id("V"), edge);
    private static Formula App(Formula function, Formula input) => Call("apply", function, input);
    private static Formula Trans(Formula graph, Formula offset, Formula input) =>
        Call("translate", graph, offset, input);
    private static Formula Shift(Formula graph, Formula input) => Call("shift", graph, input);
    private static Formula Address(Formula integer) => Call("blockAddress", Id("hk"), integer);
    private static Formula Assemble(Formula pair) => Call("assemble", Id("k"), pair);
    private static Formula BlockPair => Call("Product", Id("Int"), Call("Fin", Id("k")));
    private static Formula Edge => Call("Edge", Id("A"));

    private static Formula TranslationCommutation => All(
        All(Equal(App(Id("h"), Trans(Id("G"), Id("offset"), Id("x"))),
            Trans(Id("F"), Id("offset"), App(Id("h"), Id("x")))),
            B("offset", Id("Int")), B("x", History(Id("G")))),
        B("V", Id("Type")), B("E", Id("Type")), B("D", Id("Type")),
        B("G", Graph(Id("E"))), B("F", Graph(Id("D"))),
        B("h", Arrow(History(Id("G")), History(Id("F")))),
        B("step", All(Equal(App(Id("h"), Shift(Id("G"), Id("x"))),
            Shift(Id("F"), App(Id("h"), Id("x")))), B("x", History(Id("G"))))));
    private static Formula AssembleAddress => All(Equal(Assemble(Address(Id("i"))), Id("i")),
        B("k", Id("Nat")), B("hk", Call("NatPositive", Id("k"))), B("i", Id("Int")));
    private static Formula AddressAssemble => All(Equal(Address(Assemble(Id("pair"))), Id("pair")),
        B("k", Id("Nat")), B("hk", Call("NatPositive", Id("k"))), B("pair", BlockPair));
    private static Formula IterateTranslation => All(
        Equal(Call("iterateApply", Call("shift", Id("G")), Id("m"), Id("x")),
            Trans(Id("G"), Call("intOfNat", Id("m")), Id("x"))),
        B("V", Id("Type")), B("E", Id("Type")), B("G", Graph(Id("E"))),
        B("m", Id("Nat")), B("x", History(Id("G"))));
    private static Formula CountedEdgeIdentity => All(Equal(Id("first"), Id("second")),
        B("H", Id("Type")), B("group", Call("Group", Id("H"))),
        B("finiteH", Call("Fintype", Id("H"))), B("n", Id("Nat")),
        B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
        B("first", Edge), B("second", Edge),
        B("sameSource", Equal(Call("source", Id("first")), Call("source", Id("second")))),
        B("sameTarget", Equal(Call("target", Id("first")), Call("target", Id("second")))),
        B("sameLabel", Equal(Call("label", Id("first")), Call("label", Id("second")))),
        B("sameNumber", Equal(Call("numberValue", Id("first")), Call("numberValue", Id("second")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact integer, block and actual-edge coordinates support the constructed fixed-block code.",
        H("Coordinates for actual fixed blocks"), Blocks(
            Paragraph(Text("History(G) is the actual legal bilateral edge history. translate(G,a,x) has edge x(i+a) at every integer i. For positive k, blockAddress(hk,i) is the Euclidean quotient i/k together with the finite remainder (i mod k).toNat, and assemble(k,(j,r)) is j*k+r.val in the integers. NatPositive(k) means 0<k. These coordinates include negative positions and the case k=1.")),
            Describe.Lean(DescribeId.Create("integer-translation-commutation"),
                DeclarationHandle.Create(Prefix + "translate_commutation"), H("Unit time determines every integer translation"),
                StatementSource.FromAuthor(F.Disp(TranslationCommutation)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two directed multigraphs on the same vertex type and an arbitrary map between their actual history spaces, commutation with one forward shift implies commutation with every integer translation. No continuity, invertibility, finiteness or essentiality of the history map is assumed. This supplier is consumed by center_depends_only_on_edge, extract_edge_map and rigidity_of_fixed_block_law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("assemble-euclidean-block-address"),
                DeclarationHandle.Create(Prefix + "assemble_address"), H("Reassemble every integer position"),
                StatementSource.FromAuthor(F.Disp(AssembleAddress)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact quotient and nonnegative finite remainder reassemble the original integer, including negative positions. The parent construction uses this equation for block seams, the inverse map, the operational output, group action and block-time translation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("euclidean-address-of-assembled-pair"),
                DeclarationHandle.Create(Prefix + "address_assemble"), H("Recover the exact block and offset"),
                StatementSource.FromAuthor(F.Disp(AddressAssemble)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every integer block index and every offset in Fin(k) is recovered after assembly. The proof uses injectivity of the original assembly map and assemble_address. blockOutput_at consumes this precise pair identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shift-iterate-integer-translation"),
                DeclarationHandle.Create(Prefix + "shift_iterate_translate"), H("Natural iterates are the same translation"),
                StatementSource.FromAuthor(F.Disp(IterateTranslation)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("iterateApply(f,m,x) means Function.iterate f m applied to x, and intOfNat is the natural-to-integer coercion. The statement covers m=0 and every actual legal history. constructed_k_shift uses it in both graph spaces to turn the established k-translation equation into the k-step law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-counted-edge-coordinate-identity"),
                DeclarationHandle.Create(Prefix + "edge_eq_of_coordinates"), H("Keep every actual parallel edge"),
                StatementSource.FromAuthor(F.Disp(CountedEdgeIdentity)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An Edge(A) retains its source, target, group label and finite parallel-edge number. Equal values of all four coordinates imply equality of the actual edges, including the dependent Fin proof component. prefixLastCoordinates consumes this statement in its inverse construction; equality of labels or endpoints alone is insufficient."))), DescribeRole.Theorem),
            Paragraph(Text("The original splice construction keeps the past of one legal history and the future of another when their actual edges at zero agree. The original finite-context edge realization supplies a history containing each actual edge at zero. The counted-edge coordinate equivalence supplies the same Fintype instance used by the parent. These original suppliers are relocated directly and have retained consumers; they introduce no wrapper theorem or added mathematical assumption. Their reduced live dependencies and each module's admission remain separate current-check obligations.")),
            Paragraph(Text("The terminal original18.3 edge-rigidity, free-expansion equality and equal-power attachment statements remain in FixedBlockRigidity with the original Scribe formulas. The accepted attachment still assumes the explicit natural equality A^k=B^k. This coordinate module does not derive original dimension-group inertness, least positive tau or the rational n*b_H cutoff, and does not exclude overlapping block codes or other original-time conjugacies.")))));
}
