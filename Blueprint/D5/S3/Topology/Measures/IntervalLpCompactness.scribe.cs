using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class IntervalLpCompactnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-mesh Banach-valued averages on the whole interval are controlled by internal positive time translations.",
        H("Whole-interval mesh averages"),
        Blocks(
            Paragraph(Text("Let E be a real Banach space, d a positive real cell width, N a natural number and f a strongly measurable E-valued function integrable on Ioc(0,N*d). The i-th cell is Ioc(i*d,(i+1)*d). Its average is the Bochner integral divided by d. The mesh function takes that average on each cell and is zero outside their union. When N is zero the interval and the union are empty.")),
            Describe.Lean(DescribeId.Create("mesh-error-le"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/IntervalLpCompactness.mesh_error_le"),
                H("Internal shifts control the complete mesh error"),
                StatementSource.FromAuthor(F.Disp(MeshStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The exponent q is any real number at least one. All displayed integrals are nonnegative extended Lebesgue integrals, so the estimate remains meaningful when a power integral is infinite. No uniform norm bound on a family is used.")),
                    Paragraph(Text("Hölder's inequality bounds the power error about a cell average by the reciprocal cell measure times its two-point power error. Disjoint cells make the sum of these pair integrals at most the integral over pairs in the original interval with separation at most d. Symmetry gives twice the contribution of pairs with increasing time. The measure-preserving shear (t,h) maps to (t,t+h); the resulting domain is exactly 0<h<=d and 0<t<=N*d-h. Every sampled time lies in the original interval.")),
                    Paragraph(Text("The first and last cells participate in the same estimate. There is no residual boundary strip and no zero-extension translation hypothesis. The factor two is a proved convenient bound; no optimality is asserted.")))),
            Paragraph(Text("The underlying compactness criterion is due to Simon, Section 3, Theorem 1. His integral condition uses only strictly interior subintervals. The version with observations on all endpoint-inclusive subintervals is a stronger-hypothesis sufficiency specialization. The whole-interval estimate above is the equal-mesh proof route.")),
            Paragraph(Text("The scalar Hölder integral core and Banach average-power bound reuse the Tau Ceti contributors' immutable source leaves. Their attribution, hashes, license and replacement condition are recorded in the source and literature note.")))));

    private static Formula MeshStatement()
    {
        var t = Id("t"); var h = Id("h"); var d = Id("d"); var n = Id("N"); var q = Id("q");
        var f = Id("f"); var e = Id("E");
        var interval = Call("Ioc", F.D(0), Call("mul", n, d));
        var err = Call("power", Call("enorm", Call("sub", Call("f", t), Call("meshAverage", d, n, f, t))), q);
        var inc = Call("power", Call("enorm", Call("sub", Call("f", Call("add", t, h)), Call("f", t))), q);
        return All("E", Id("Types"), All("d", Id("Real"), All("N", Id("Nat"),
            All("f", new Formula.TypeArrow(Id("Real"), e), All("q", Id("Real"),
                Implies(And(Call("RealBanach", e), Lt(F.D(0), d), Call("StronglyMeasurable", f),
                        Call("IntegrableOn", f, interval), Le(F.D(1), q)),
                    Le(Call("LIntegralOn", interval, t, err),
                        Call("mul", Call("inv", Call("ofReal", d)), Call("mul", F.D(2),
                            Call("LIntegralOn", Call("Ioc", F.D(0), d), h,
                                Call("LIntegralOn", Call("Ioc", F.D(0), Call("sub", Call("mul", n, d), h)), t, inc))))))))));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Id(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula And(params Formula[] clauses)
    {
        var r = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--) r = new Formula.Logic(clauses[i], FormulaLogicOperator.And, r);
        return r;
    }
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Le, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Lt, b);
}
