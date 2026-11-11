using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Heisenberg;

internal sealed class DeterminantChartsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/Heisenberg/DeterminantCharts.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residue coordinates give an all-pairs bijection preserving determinant-zero incidence.",
        H("Fine slopes and residue directions"), Blocks(
            Describe.Lean(DescribeId.Create("residue-incidence-bijection"),
                DeclarationHandle.Create(Owner + "determinantEquiv_preserves"),
                H("Equality of cross products is transported for every pair"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("R and S are commutative rings and K is a field, all in arbitrary universes. A ResidueCoordinates value supplies an equivalence code from its ring to K times K, a residue ring homomorphism res, and the laws res(x)=first(code(x)), code(0)=(0,0), IsUnit(x) iff res(x) is nonzero, and j(a)*x=j(a*res(x)), where j(a)=code inverse (0,a). These laws are explicit premises of this reusable theorem. The two coefficient-ring values used in the group construction prove all these laws directly.")),
                    Paragraph(Text("Chart R K is the disjoint sum of pairs (u,t) with u a unit and t in R, pairs (s,u) with s in K and u a unit, and pairs (a,b) in K times K. Decode sends them respectively to (u,u*t), (u*j(s),u) and (j(a),j(b)). It is bijective: test whether the first coordinate is a unit, then whether the second is a unit. In the remaining case both coordinates are in the kernel of res and have unique j coordinates. Unit cancellation proves uniqueness within each chart; the two residue-zero tests separate the charts.")),
                    Paragraph(Text("For two first-chart vectors incidence means equality of t. For two second-chart vectors it means equality of s. The first and second charts are never incident to each other. Between a first-chart vector with slope t and a third-chart vector (a,b), incidence is b=res(t)*a. Between a second-chart vector and a third-chart vector it is a=0. Every two third-chart vectors are incident because the ideal squares to zero. The reverse ordered cases have the same relation. These nine rules include zero and equal vectors.")),
                    Paragraph(Text("Code identifies both coefficient carriers with K times K and both unit carriers with the subtype whose first coordinate is nonzero. Applying these equivalences to the charts produces the same normal-form carrier for R and S, with the same nine incidence rules. Composing the two normal forms gives determinantEquiv C D. The displayed cross-product equality is equivalent to determinant zero by subtracting the right side; no distant or determinant-unit relation is substituted."))),
                DescribeRole.Theorem))));

    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Inst(string n, Formula t, Formula b) => Seq(OpenBracket, Call(n, t), CloseBracket, Sp, b);
    private static Formula Pair(Formula a) => Call("Prod", a, a);
    private static Formula Det(Formula v, Formula w) => Eq(Call("mul", Call("fst", v), Call("snd", w)), Call("mul", Call("fst", w), Call("snd", v)));
    private static Formula Statement()
    {
        var r = F.Id("R"); var k = F.Id("K"); var s = F.Id("S");
        var c = F.Id("C"); var d = F.Id("D"); var v = F.Id("v"); var w = F.Id("w");
        return All("R", Call("Type"), All("K", Call("Type"), Inst("CommRing", r, Inst("Field", k,
            All("C", Call("ResidueCoordinates", r, k), All("S", Call("Type"), Inst("CommRing", s,
                All("D", Call("ResidueCoordinates", s, k), All("v", Pair(r), All("w", Pair(r),
                    Iff(Det(v,w), Det(Call("determinantEquiv", c,d,v), Call("determinantEquiv", c,d,w)))))))))))));
    }
}
