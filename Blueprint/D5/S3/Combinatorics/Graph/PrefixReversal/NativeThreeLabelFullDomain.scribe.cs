using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeThreeLabelFullDomainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete actual supply frame with three residual labels already describes every permutation, including at the final outer parent.",
        H("Three Residual Labels Give the Full Native Cayley Graph"),
        Blocks(
            Theorem("native_three_label_frame_domain", "The Final Marked Layer Is the Whole Group", DomainFormula(false),
                "For every m and k and every complete SupplyFrame(m,k), a base of length two leaves exactly terminal plus those two base labels after deleting the selected labels. Every actual configuration belongs to this independently specified layer. Full nodup and complete-label obligations earn the residual membership equivalence; injectivity of the actual permutation earns the filtered list permutation. The existing three-label circular-order lemma then yields the base circle or its reverse. Neither a candidate scan nor a cardinality comparison supplies coverage."),
            Theorem("native_three_label_parent_domain", "The Last Outer Parent Is the Whole Group", DomainFormula(true),
                "For the last outer supply, delete the terminal as well as the selected labels. If the literal base has length three, its residual bracelet contains every actual permutation. The proof derives the exact remaining-label condition directly from the complete frame and applies the same genuine three-label order argument. This is the independent full parent domain required at the stopping layer of the all-size recursive construction."),
            Definition("fullDomainIso", "Identity from the Full Marked Layer", IsoFormula(false),
                "The vertex map is Subtype.val. Its surjectivity is earned by native_three_label_frame_domain and its injectivity is subtype injectivity. Adjacency is exactly the same native a/b/c Cayley adjacency, so this is a graph isomorphism on actual configurations."),
            Definition("fullParentDomainIso", "Identity from the Full Outer Parent", IsoFormula(true),
                "The same identity on configurations is a graph isomorphism from the final three-label parent domain to the full three-generator Cayley graph. Mapping an already constructed parent walk along it preserves that very walk's Hamiltonicity, vertices and edges. These domain theorems do not assume or independently construct the recursive Hamilton cycle."))));

    private static DocumentBlock Theorem(string selector, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(selector.Replace('_', '-')), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Theorem);
    private static DocumentBlock Definition(string selector, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(selector.ToLowerInvariant()), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Definition);
    private static Formula Selected(bool parent) => parent
        ? Call("Insert", Call("Terminal", F.Id("frame")), Call("ToFinset", Call("Selected", F.Id("frame"))))
        : Call("ToFinset", Call("Selected", F.Id("frame")));
    private static Formula Residual(bool parent) => Call("CycleOfList", parent
        ? Call("Base", F.Id("frame"))
        : Call("Cons", Call("Terminal", F.Id("frame")), Call("Base", F.Id("frame"))));
    private static Formula StoppingFormula(bool parent, Formula body) => Disp(All("m", Call("Nat"), All("k", Call("Nat"),
        All("frame", Call("SupplyFrame", F.Id("m"), F.Id("k")),
            Implies(Eq(Call("Length", Call("Base", F.Id("frame"))), parent ? D(3) : D(2)),
                body)))));
    private static Formula DomainFormula(bool parent) => StoppingFormula(parent,
        All("v", Call("Configuration", F.Id("m")),
            Call("Layer", Selected(parent), Residual(parent), F.Id("v"))));
    private static Formula IsoFormula(bool parent) => StoppingFormula(parent, Call("GraphIso",
        Call("DomainGraph", Call("Layer", Selected(parent), Residual(parent))),
        Call("MulCayley", Call("NativeGenerators", F.Id("m")))));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
