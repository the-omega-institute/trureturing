using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class ActiveSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/ActiveSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every parameter t at least two, the actual edge support of a native balanced labelled zigzag choice has at most two weak components.",
        H("Actual Active Support of Zigzag Choices"),
        Blocks(
            Paragraph(Text(
                "The objects are the native Choices t: one labelled form for each class from 2 through 3t-2, "
                + "with class two restricted to II, III, IV, and V. The endpoint formulas are those of "
                + "Feldman's The Missing Zigzag (arXiv:2609.26114v1), Section 5 equation (2). Balance is the existing integer "
                + "outdegree minus indegree condition at each nonzero residue. The support statements below are derived from "
                + "these objects; they impose no closure condition and identify no choices under reflection or rotation.")),
            Describe.Lean(DescribeId.Create("actual-active-vertices"),
                DeclarationHandle.Create(Prefix + "Active"), H("Endpoints of selected class edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A residue is active exactly when it is an endpoint of a selected formPair. "
                    + "The original finite class index is the witness. ActiveVertex is the subtype of "
                    + "these residues, so unused vertices are absent."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-weak-components"),
                DeclarationHandle.Create(Prefix + "ActiveComponent"), H("Weak components of actual support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "SupportArrow has precisely the selected directed endpoint pairs, witnessed by their "
                    + "class labels. Its equivalence closure forgets orientation for reachability. Restricting "
                    + "that equivalence to ActiveVertex and taking the quotient gives the actual weak "
                    + "components. This equivalence identifies vertices, never the underlying labelled choices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("active-component-bound"),
                DeclarationHandle.Create(Prefix + "active_component_count_le_two"),
                H("At most two actual active components"), StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every t at least two and every native balanced choice c, the natural cardinality "
                    + "of ActiveComponent c is at most two. The native complete parity correspondences "
                    + "express c as a signed retirement path. Every endpoint of the starting edge reaches "
                    + "a semitone vertex. Each subsequent pair attaches to a semitone or to an already "
                    + "anchored frontier with nonzero charge. Both the even antipodal pair and the odd "
                    + "singleton preserve anchoring. Hence every actual component contains an actually "
                    + "used semitone. The subtype of used semitones, which may have only one element, "
                    + "surjects onto the component quotient and has cardinality at most two."))),
                DescribeRole.Theorem)), []));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula BoundFormula()
    {
        Formula t = F.Id("t"), c = F.Id("c");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        return Disp(All("t", nat, Imp(Le(D(2), t),
            All("c", Call("Choices", t), Imp(Call("Balanced", c),
                Le(Call("activeComponentCount", c), D(2)))))));
    }
}
