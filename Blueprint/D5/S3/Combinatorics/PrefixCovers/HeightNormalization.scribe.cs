using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PrefixCovers;

internal sealed class HeightNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PrefixCovers/HeightNormalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite labelled cover by prefix cylinders can be shortened to a depth bounded by its surviving number of members and the target's fixed prefix length.",
        H("Finite Height Normalization for Labelled Prefix Covers"),
        Blocks(
            Paragraph(Text(
                "Let the alphabet, index type, label type and side-coordinate type be arbitrary types. "
                + "Fix an alphabet element a and a natural number r. A stream is a function from the natural numbers to the alphabet. "
                + "Prefix(k,x,w) means x(t)=w(t) for every t<k. An indexed cover consists of a finite index set I, "
                + "positive depths h(i)>r, reference streams w(i), labels c(i), and side predicates T(i,z). "
                + "The target predicate E(x,z) depends on x only through its first r symbols: agreement there transports membership in E. "
                + "Covers(I,h,w,T,E) means that every point of E satisfies Prefix(h(i),x,w(i)) and T(i,z) for some i in I. "
                + "DistinctLabels means that the pairs (h(i),c(i)) are injective on I; the label c(i) alone may repeat at different depths.")),
            Describe.Lean(DescribeId.Create("normalization"),
                DeclarationHandle.Create(Prefix + "normalize_cover"),
                H("A Bound by the Number of Surviving Members"),
                StatementSource.FromAuthor(NormalizationFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under these hypotheses there are J contained in I, new depths h' and new streams w' such that "
                        + "every i in J satisfies r<h'(i)<=r+|J| and h'(i)<=h(i), and w'(i) agrees with w(i) on its first r symbols. "
                        + "The pairs (h'(i),c(i)) remain injective on J, and the cylinders still cover the same E with the original side predicates T. "
                        + "Thus the side coordinate, its permitted sets, and the old prefix symbols are preserved. No finiteness assumption "
                        + "is imposed on the alphabet or on the side-coordinate type. Empty index sets and empty targets are allowed when the coverage premise holds.")),
                    Paragraph(Text(
                        "If some used depth K exceeds r+|I|, cardinality of the integer interval from r+1 through K yields an unused depth g. "
                        + "Insert the fixed symbol a at stream position g-1 and take inverse images of the original covering cylinders. "
                        + "Depths below g are unchanged. A cylinder of depth above g disappears when its prescribed symbol at g-1 is not a; "
                        + "otherwise it shortens by one and deletes that symbol from its reference stream. "
                        + "The target is unchanged under this inverse image because g-1>=r. "
                        + "There was no cylinder at depth g, so shortened and unchanged height-label pairs cannot collide. "
                        + "The sum of all retained depths strictly decreases, giving a terminating induction.")),
                    Paragraph(Text(
                        "For any nonnegative per-member costs that are nondecreasing with depth, "
                        + "the resulting total cost does not increase: retained depths decrease and removed members contribute nothing. "
                        + "With r=2 and at most M original members, every surviving depth is at most M+2. "
                        + "This is a conditional normalization of an existing prefix cover. It neither constructs a cover from fractional data "
                        + "nor proves that a congruence system has such a replacement. Applying it to arithmetic progressions requires "
                        + "a separate coordinate correspondence and a proof that numerical label distinctness is equivalent to the stated pair condition."))),
                DescribeRole.Theorem))));

    private static Formula NormalizationFormula()
    {
        var input = And(Call("TargetDependsOnPrefix", F.Id("E"), F.Id("r")),
            And(Call("DepthsAbove", F.Id("I"), F.Id("h"), F.Id("r")),
                And(Call("DistinctLabels", F.Id("I"), F.Id("h"), F.Id("c")),
                    Call("Covers", F.Id("I"), F.Id("h"), F.Id("w"), F.Id("T"), F.Id("E")))));
        var output = And(Call("Subset", F.Id("J"), F.Id("I")),
            And(Call("PointwiseDepthBoundsAndOldPrefixAgreement", F.Id("J"), F.Id("hnew"), F.Id("wnew"), F.Id("h"), F.Id("w"), F.Id("r")),
                And(Call("DistinctLabels", F.Id("J"), F.Id("hnew"), F.Id("c")),
                    Call("Covers", F.Id("J"), F.Id("hnew"), F.Id("wnew"), F.Id("T"), F.Id("E")))));
        var body = Implies(input, Exists("J", Call("Finset", F.Id("Index")),
            Exists("hnew", Call("Function", F.Id("Index"), F.Id("Nat")),
                Exists("wnew", Call("Function", F.Id("Index"), F.Id("Stream")), output))));
        body = All("a", F.Id("Alphabet"), body);
        body = All("r", F.Id("Nat"), body);
        body = All("E", Call("TargetPredicate", F.Id("Stream"), F.Id("Side")), body);
        body = All("T", Call("SidePredicates", F.Id("Index"), F.Id("Side")), body);
        body = All("c", Call("Function", F.Id("Index"), F.Id("Label")), body);
        body = All("w", Call("Function", F.Id("Index"), F.Id("Stream")), body);
        body = All("h", Call("Function", F.Id("Index"), F.Id("Nat")), body);
        return Disp(All("I", Call("Finset", F.Id("Index")), body));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
}
