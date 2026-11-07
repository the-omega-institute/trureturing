using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class OrderUnitCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completion of the specified order-unit norm retains exactly the original cone and unit.",
        H("Faithful completion of an order-unit space"),
        Blocks(
            Paragraph(Text("Let E be any real normed vector space and let A be OrderUnitNorm.Data on E: a closed salient convex cone C containing zero, with specified interior unit u. Assume the original norm equals A.orderNorm at every original vector. The equality is an actual hypothesis about that specified norm. No finite dimension, completeness or nonzero dimension is assumed.")),
            Paragraph(Text("X is UniformSpace.Completion E in the original norm, and i is UniformSpace.Completion.toComplₗᵢ, the canonical real linear isometry with dense range. completedCone(A) is exactly the closure in X of i(C). completedData(A) has that cone and i(u) as its unit; only its required proofs are constructed. The notation B below denotes this actual completedData, whose construction depends on the stated norm equality.")),
            Describe.Lean(DescribeId.Create("faithful-order-unit-completion"),
                DeclarationHandle.Create("D5/S3/Topology/OrderUnitCompletion.faithful_completion"),
                H("Exact order intervals and faithful cone restriction"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("RealNormedVectorSpace includes the additive group and real normed-space instances. Types is the type universe, R is the real field, and Data(E) is precisely the original cone-unit data. Completion, Embed, CompletedData, Cone, Unit, Norm and OrderNorm refer to the constructions just specified. Every completed vector and every real radius are quantified, including negative radii. The radius condition explicitly includes nonnegativity, so it remains exact when E is zero.")),
                    Paragraph(Text("The existing original norm_le_iff supplies attained order endpoints. For original positive vectors b,c, the order endpoints for b+c and cone addition bound the norm of b-c by the norm of b+c. Two successive closed-set arguments extend this difference bound to arbitrary positive vectors in the completed cone. Applying it to r i(u)-x and r i(u)+x gives the reverse completed interval estimate, using the original bound norm(u) at most one. This estimate is used in the delivered theorem, including in the proof that the completed cone is salient.")),
                    Paragraph(Text("Completion induction extends the original attained norm endpoints to every x in X. Adding a nonnegative multiple of i(u) gives all larger radii. The unit ball translated to i(u) is contained in the cone, proving the interior-unit requirement. The exact completed interval characterization and the original definition of orderNorm as an infimum then identify the completed order norm with the original completion norm. The canonical embedding induces the original topology; closedness of C therefore gives i(a) in the completed cone if and only if a in C.")),
                    Paragraph(Text("This is the order-unit completion subclaim in the completion paragraph of the original Unit 2.2 proof and the same-cone, same-norm requirement of Unit 6.1, in AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE. Order-unit completion is mature mathematics; no novelty is claimed. The present result supplies neither extension of the original multiplication S nor window approximation, zero-face dynamics, the unit law, Jordan or JB identification. Both original source entrances and all original S,C,u,N,theta and physical consumers retain their original quantifiers in the unresolved parent. Positive evaluations, including zero mass, are not removed or normalized; their continuous extension and the remaining product arguments are separate obligations.")))))));

    private static Formula Statement()
    {
        var E = Id("E"); var A = Id("A"); var a = Id("a"); var x = Id("x"); var r = Id("r");
        var X = Call("Completion", E);
        var B = Call("CompletedData", A);
        var u = Call("Unit", B); var C = Call("Cone", B);
        var normAgreement = All("a", E, Eq(Call("Norm", a), Call("OrderNorm", A, a)));
        var intervals = All("x", X, All("r", Id("R"), Iff(Le(Call("Norm", x), r),
            And(Le(F.D(0), r), Mem(Sub(Scale(r, u), x), C), Mem(Add(Scale(r, u), x), C)))));
        var norm = All("x", X, Eq(Call("OrderNorm", B, x), Call("Norm", x)));
        var pullback = All("a", E, Iff(Mem(Call("Embed", a), C), Mem(a, Call("Cone", A))));
        return All("E", Id("Types"), Implies(Call("RealNormedVectorSpace", E),
            All("A", Call("Data", E), Implies(normAgreement, And(intervals, norm, pullback)))));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Id(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula And(params Formula[] xs)
    {
        var result = xs[^1];
        for (var j = xs.Length - 2; j >= 0; j--) result = new Formula.Logic(xs[j], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => F.Seq(a, F.Sp, F.Le, F.Sp, b);
    private static Formula Mem(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => F.Seq(a, F.Sp, F.Plus, F.Sp, b);
    private static Formula Sub(Formula a, Formula b) => F.Seq(a, F.Sp, F.Minus, F.Sp, b);
    private static Formula Scale(Formula a, Formula b) => Call("smul", a, b);
}
