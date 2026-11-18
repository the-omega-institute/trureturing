using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class GainPotentialStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform triangle defects bound simultaneous vertex-potential errors on finite chordal graphs.",
        H("Stability of chordal group gain potentials"),
        Blocks(
            Paragraph(Text("Let V be a finite vertex type and H a group with a pseudometric invariant under both left and right multiplication. An oriented edge from i to j carries a label g(i,j). Reversing an edge inverts its label exactly. For each ordered triangle, the distance between g(i,j)g(j,k) and g(i,k) is at most a common nonnegative real number epsilon.")),
            Describe.Lean(
                DescribeId.Create("chordal-gain-potential-stability"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/GainPotentialStability.exists_approximate_gain_potential"),
                H("A simultaneous approximate potential"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here NatCard is the finite cardinality, NatSub denotes subtraction truncated at zero in the natural numbers, and NatToReal is the natural-number embedding into the reals. Thus the coefficient is exactly max(cardinality(V) minus two, zero). The assumptions IsIsometricSMul(H,H) and IsIsometricSMul(MulOpposite(H),H) express invariance under left and right translation. The existential quantifier selects one potential phi that satisfies the displayed error bound on every oriented edge simultaneously.")),
                    Paragraph(Text("Induct on a finite set s of vertices, with error coefficient NatSub(cardinality(s),2). Chordality of the induced graph supplies a simplicial vertex x. Remove x and construct a potential psi on the remaining vertices. If x has no remaining neighbor, keep psi. Otherwise choose a neighbor w and set phi(x) = psi(w) times the inverse of g(x,w), leaving other values unchanged. This satisfies the edge from x to w exactly.")),
                    Paragraph(Text("For another neighbor j distinct from w, simpliciality supplies the edge from w to j. The metric triangle inequality bounds the new edge error by the triangle defect at (x,w,j) plus the inherited error on (w,j). Left translation preserves that inherited distance. Since x,w,j are distinct, s has at least three vertices, and adding one to NatSub(cardinality(s) minus one,2) gives NatSub(cardinality(s),2). The opposite orientation has the same error because inversion is an isometry under the two translation assumptions. The inherited edges satisfy the enlarged bound by nonnegativity of epsilon.")),
                    Paragraph(Text("The group may be noncommutative and may lie in an arbitrary universe. The graph may be empty or disconnected. Values of the total label function on nonedges and on the diagonal are unrestricted. The theorem assumes no completeness, compactness, finite group, diameter bound, or previously supplied potential. At epsilon zero the conclusion is zero distance on every edge; a pseudometric alone does not turn zero distance into equality. Equality follows when the pseudometric separates points.")),
                    Paragraph(Text("The result is an existence and uniform error estimate for deterministic triangle constraints. It makes no assertion of optimality of the coefficient, statistical recovery, latent-state identification, or executable running time. Lerman and Shi, Robust Group Synchronization via Cycle-Edge Message Passing, https://arxiv.org/abs/1912.11347v3 , provides background on synchronization with bi-invariant metrics. Its corruption and iterative recovery models impose additional assumptions and do not supply this chordal triangle-only existence statement."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Statement()
    {
        var v = F.Id("V");
        var h = F.Id("H");
        var graph = F.Id("G");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        var eps = F.Id("epsilon");
        Formula adj(Formula a, Formula b) => Call("Adj", graph, a, b);
        Formula gain(Formula a, Formula b) => Call("g", a, b);
        Formula pot(Formula a) => Call("phi", a);
        var reversal = All("i", v, All("j", v,
            Imp(adj(i, j), Eqn(gain(j, i), Call("inv", gain(i, j))))));
        var triangle = All("i", v, All("j", v, All("k", v,
            Imp(adj(i, j), Imp(adj(j, k), Imp(adj(i, k),
                Le(Call("dist", Mul(gain(i, j), gain(j, k)), gain(i, k)), eps)))))));
        var coefficient = Call("NatToReal", Call("NatSub", Call("NatCard", v), D(2)));
        Formula result = Some("phi", new Formula.TypeArrow(v, h),
            All("i", v, All("j", v, Imp(adj(i, j),
                Le(Call("dist", gain(i, j), Mul(Call("inv", pot(i)), pot(j))),
                    Mul(coefficient, eps))))));
        result = Imp(reversal, Imp(triangle, result));
        result = All("epsilon", Call("Real"), Imp(Le(D(0), eps), result));
        result = All("g", new Formula.TypeArrow(v, new Formula.TypeArrow(v, h)), result);
        result = All("G", Call("SimpleGraph", v), Imp(Call("IsChordal", graph), result));
        result = Seq(
            OpenBracket, Call("Finite", v), CloseBracket, Sp,
            OpenBracket, Call("Group", h), CloseBracket, Sp,
            OpenBracket, Call("PseudoMetricSpace", h), CloseBracket, Sp,
            OpenBracket, Call("IsIsometricSMul", h, h), CloseBracket, Sp,
            OpenBracket, Call("IsIsometricSMul", Call("MulOpposite", h), h),
                CloseBracket, Comma, Sp, result);
        result = All("V", Call("Type", F.Id("u")), All("H", Call("Type", F.Id("v")), result));
        return All("u", Call("Universe"), All("v", Call("Universe"), result));
    }
}
