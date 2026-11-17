using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class LocalLeafInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/LocalLeafInverse.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local singleton fibres control the inverse error of two finite observation channels.",
        H("Stable Recovery from Opposite-Channel Singleton Fibres"), Blocks(
            Paragraph(Text("Let X, U and V be finite types and let f:X->U and g:X->V be the actual deterministic observations. "
                + "A point x is an f-leaf if every y with f(y)=f(x) equals x. OppositeLeaves(f,g) means that whenever x is not a leaf in either channel, every different y in its f-fibre is a g-leaf. Both channel orientations are assumed. These are conditions on the complete fibres of the supplied maps, independent of any weights or desired inverse estimate.")),
            Paragraph(Text("In the formulas, Weights(X) is X->Real, L1(h) is the sum over X of abs(h(x)), "
                + "pushMass(f,h)(u) is the sum of h over the actual fibre f(x)=u, and TV(p,q) is one half of L1(p-q). "
                + "Empty finite types and signed weights are allowed; no normalization, positivity, or zero-total-mass assumption is used.")),
            Describe.Lean(DescribeId.Create("signed-inverse-bound"),
                DeclarationHandle.Create(Prefix + "signed_l1_le"),
                H("Uniform signed inverse estimate"),
                StatementSource.FromAuthor(Signed()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Call a point a centre if neither observation identifies it alone. At most one centre uses each output coordinate: a second centre in that fibre would have to be an opposite-channel leaf. Partners of distinct centres therefore occupy disjoint singleton fibres in the other channel. "
                    + "The fibre triangle inequality bounds twice the centre mass by the two centre-output norms plus the two leaf masses. Every noncentre is a leaf in at least one channel. Leaf and centre outputs are disjoint, so no observed coordinate is charged twice. The resulting signed L1 bound has coefficient three halves."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tv-inverse-bound"),
                DeclarationHandle.Create(Prefix + "total_variation_le_sum"),
                H("Total-variation error bound"),
                StatementSource.FromAuthor(Variation()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the signed estimate to p-q, use linearity of the actual pushforward, and divide by two. "
                    + "Probability mass functions are included. If both observed TV errors are at most epsilon, the source TV is at most three epsilon. The bound uses the sum of the separate errors and does not assume a joint law for the two channel outputs."))),
                DescribeRole.Theorem),
            Paragraph(Text("The local condition permits double-star incidence components with degrees larger than two. "
                + "Consequently, it does not require a global enumeration of graph components, a path partition, or a degree-two hypothesis. "
                + "The coefficient is an upper bound under the stated local condition; optimality in a particular observation model requires its own witnesses.")))));

    private static Formula Premise() => And(Call("OppositeLeaves", I("f"), I("g")),
        Call("OppositeLeaves", I("g"), I("f")));
    private static Formula Signed()
    {
        var observed = Add(Call("L1", Call("pushMass", I("f"), I("h"))),
            Call("L1", Call("pushMass", I("g"), I("h"))));
        var bound = Leq(Call("L1", I("h")),
            Multiply(Seq(Frac, Grp(D(3)), Grp(D(2))), observed));
        return Quantify(All("h", Call("Weights", I("X")), Imp(Premise(), bound)));
    }
    private static Formula Variation()
    {
        var observed = Add(
            Call("TV", Call("pushMass", I("f"), I("p")), Call("pushMass", I("f"), I("q"))),
            Call("TV", Call("pushMass", I("g"), I("p")), Call("pushMass", I("g"), I("q"))));
        var bound = Leq(Call("TV", I("p"), I("q")),
            Multiply(Seq(Frac, Grp(D(3)), Grp(D(2))), observed));
        return Quantify(All("p", Call("Weights", I("X")),
            All("q", Call("Weights", I("X")), Imp(Premise(), bound))));
    }
    private static Formula Quantify(Formula body) => Disp(All("X", Call("FiniteType"),
        All("U", Call("FiniteType"), All("V", Call("FiniteType"),
            All("f", Call("Function", I("X"), I("U")),
                All("g", Call("Function", I("X"), I("V")), body))))));
    private static Formula I(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Seq(Open,a,Close), FormulaLogicOperator.And, Seq(Open,b,Close));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Seq(Open,a,Close), FormulaLogicOperator.Implies, Seq(Open,b,Close));
}
