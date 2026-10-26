using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class AndrasfaiWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual labelled subsets are equivalent to their Boolean membership functions, and original-host visibility is exactly periodic forbidden-factor avoidance.",
        H("Actual membership words and cyclic boundaries"),
        Blocks(
            Node("membership-labels", "Canonical Boolean labels", "membershipLabels", null,
                "For every natural m, subset X of Z/(3m+2)Z and i in Fin(3m+2), the label at i is the Boolean decision that the vertex represented by i.val belongs to X. The vertex names and origin are fixed.", DescribeRole.Definition),
            Node("membership-word", "The finite membership word", "membershipWord", null,
                "The word is List.ofFn of the canonical membership labels. It lists every original host vertex once in increasing representative order.", DescribeRole.Definition),
            Node("subset-of-labels", "Decode the labels", "subsetOfLabels", null,
                "The inverse includes precisely those actual vertices v whose Boolean label at the representative v.val is true.", DescribeRole.Definition),
            Node("subset-labels-equivalence", "Equivalence of actual subsets and labels", "subsetLabelsEquiv", null,
                "For every m, this is an equivalence from Finset(Vertex m) to Fin(3m+2) -> Bool. Its forward map is membershipLabels and its inverse is subsetOfLabels. Both inverse identities are proved using the canonical representatives. There is no quotient by cyclic rotation and no restriction to maximal or independent subsets.", DescribeRole.Definition),
            Node("membership-word-length", "Full original host length", "membership_word_length", LengthFormula(),
                "For every m and every actual vertex subset X, the finite membership word has length 3m+2.", DescribeRole.Theorem),
            Node("visibility-periodic-word", "The complete cyclic boundary bridge", "visible_iff_word_periodic_avoidance", VisibilityFormula(),
                "For every m >= 1 and every actual subset X, Visible(host m,X), using shortest paths in the original host, is equivalent to PeriodicAvoidance(membershipWord m X). The proof first characterizes ContainsForbidden in an arbitrary finite indexed block by a start a and positive k with a+3k within the block, selected first and last letters, and selected positions a+1+3j for all j<k. Induction on Triples proves the forward direction; splitting List.ofFn blocks constructs the reverse direction. Repeated words are indexed by the same natural positions interpreted in Z/(3m+2)Z. Every finite forbidden occurrence therefore gives an actual cyclic ForbiddenFactor. Conversely, for an arbitrary cyclic start u and arbitrary positive k, the representative a=u.val and a+3k complete copies provide enough room to realize the whole factor, even across the origin or across many periods. The existing original-host periodic-obstruction theorem then proves the stated equivalence. The supplier's private copies function is related to List.replicate followed by flatten by definitional unfolding and induction; no supplier exposure or assumed boundary alignment is used.", DescribeRole.Theorem),
            Node("count-zero", "The actual index-one count", "count_zero",
                Disp(new Formula.Relation(Call("count", D(0)), FormulaRelationOperator.Equal, D(4))),
                "The original index-one graph has two vertices. Its obstruction predicate is impossible because it would require a positive k at most zero, so every actual subset is visible. An explicit equivalence from the actual Configuration type to all vertex subsets, followed by the finite powerset cardinality, gives exactly four. This is the actual original-host count, independently of any automaton trace.", DescribeRole.Theorem),
            Paragraph(Text("The consuming count-identification proof may use subsetLabelsEquiv, membership_word_length and visible_iff_word_periodic_avoidance to identify actual labelled configurations with periodic admissible words. The matrix trace counting correspondence and full actual-count generating series are separate obligations; count_zero supplies the actual index-one correction. This module does not assert a complete resolution of A391632."))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Order(Formula m) => Call("add", Call("mul", D(3), m), D(2));

    private static Formula LengthFormula()
    {
        var m = F.Id("m");
        var x = F.Id("X");
        return Disp(All("m", Call("Nat"), All("X", Call("Finset", Call("Vertex", m)),
            new Formula.Relation(Call("length", Call("membershipWord", m, x)),
                FormulaRelationOperator.Equal, Order(m)))));
    }

    private static Formula VisibilityFormula()
    {
        var m = F.Id("m");
        var x = F.Id("X");
        return Disp(All("m", Call("Nat"),
            new Formula.Logic(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, m),
                FormulaLogicOperator.Implies,
                All("X", Call("Finset", Call("Vertex", m)),
                    new Formula.Logic(Call("Visible", Call("host", m), x),
                        FormulaLogicOperator.Iff,
                        Call("PeriodicAvoidance", Call("membershipWord", m, x)))))));
    }
}
