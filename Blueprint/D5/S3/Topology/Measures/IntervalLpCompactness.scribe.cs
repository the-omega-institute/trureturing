using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class IntervalLpCompactnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact interval integrals and uniform internal positive time translations give compact closure in Banach-valued Lp.",
        H("Compactness from interval integrals and internal translations"),
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
            Describe.Lean(DescribeId.Create("compactness-criterion"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/IntervalLpCompactness.isCompact_closure_of_integrals_translations"),
                H("Compact closure in the actual Lp space"),
                StatementSource.FromAuthor(F.Disp(CompactnessStatement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/simon1986compact")),
                Blocks(
                    Paragraph(Text("E is an arbitrary real Banach space in any universe. T is positive, p is any ENNReal exponent with 1<=p and p different from infinity, and S is any subset of Lp(E,p,volume restricted to Ioc(0,T)). S may be empty. For every 0<=a<b<=T, assume compact closure in E of the image of S under its Bochner integral on Ioc(a,b). For every positive real epsilon assume a positive delta such that all f in S and all 0<h<delta with h<T have internal eLpNorm less than ofReal(epsilon). Internal means that both times t and t+h lie in the original interval, and the norm is taken over Ioc(0,T-h).")),
                    Paragraph(Text("For any tolerance choose a mesh width T/N smaller than delta and T. The preceding estimate makes each function uniformly close in the actual Lp metric to its mesh average. The average coefficients belong to compact sets obtained from the compact closures of the interval-integral images by multiplication by the reciprocal cell measure. Their finite product is compact. Summing indicatorConstLp values is continuous, so the mesh averages lie in a compact subset of the same Lp space. Uniform approximation transfers total boundedness, and completeness of Lp gives compact closure.")),
                    Paragraph(Text("The argument includes p=1 and infinite-dimensional targets. It adds no separate uniform Lp bound, reflexivity, separability, pointwise time modulus, continuous representative or whole-line translation hypothesis. Lebesgue AE replacement preserves both the subinterval integrals and the internal translation expression: positive translation transports null sets between the restricted intervals. The canonical representatives are used only to express these class-invariant quantities.")),
                    Paragraph(Text("Simon, Section 3, Theorem 1, proves an equivalence using only strictly interior integral observations 0<a<b<T. The present endpoint-inclusive integral assumption is stronger and the conclusion is its sufficiency direction. It is not the full original equivalence. The equal-mesh estimate treats both ends simultaneously.")))),
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
    private static Formula CompactnessStatement()
    {
        var e = Id("E"); var p = Id("p"); var t = Id("T"); var s = Id("S");
        var a = Id("a"); var b = Id("b"); var h = Id("h"); var eps = Id("epsilon"); var delta = Id("delta"); var f = Id("f");
        var lp = Call("Lp", e, p, Call("RestrictedVolume", Call("Ioc", F.D(0), t)));
        var integrals = All("a", Id("Real"), All("b", Id("Real"),
            Implies(And(Le(F.D(0), a), Lt(a, b), Le(b, t)),
                Call("IsCompact", Call("closure", Call("image", Call("IntervalIntegral", a, b), s))))));
        var translations = All("epsilon", Id("Real"), Implies(Lt(F.D(0), eps),
            Exists("delta", Id("Real"), And(Lt(F.D(0), delta),
                All("h", Id("Real"), Implies(And(Lt(F.D(0), h), Lt(h, delta), Lt(h, t)),
                    All("f", lp, Implies(Call("Member", f, s),
                        Lt(Call("eLpNorm", Call("InternalDifference", f, h), p,
                            Call("RestrictedVolume", Call("Ioc", F.D(0), Call("sub", t, h)))),
                            Call("ofReal", eps))))))))));
        return All("E", Id("Types"), All("T", Id("Real"), All("p", Id("ENNReal"),
            All("S", Call("Set", lp), Implies(
                And(Call("RealBanach", e), Lt(F.D(0), t), Le(F.D(1), p),
                    new Formula.Relation(p, FormulaRelationOperator.NotEqual, F.Infty), integrals, translations),
                Call("IsCompact", Call("closure", s)))))));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Id(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Exists(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), type, body);
    private static Formula And(params Formula[] clauses)
    {
        var r = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--) r = new Formula.Logic(clauses[i], FormulaLogicOperator.And, r);
        return r;
    }
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
}
