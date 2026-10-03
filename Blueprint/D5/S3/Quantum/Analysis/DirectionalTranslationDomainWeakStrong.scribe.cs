using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class DirectionalTranslationDomainWeakStrongDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directional weak differentiation and norm differentiation of actual L2 translations agree in every finite Euclidean dimension.",
        H("Directional Translation Domains"),
        Blocks(Describe.Lean(
            DescribeId.Create("directional-translation-domain-iff"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/DirectionalTranslationDomainWeakStrong.directional_translation_domain_iff"),
            H("Weak and strong directional derivatives"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For each natural number n, E(n) is EuclideanSpace Real (Fin n), with its Lebesgue measure volume. "
                    + "Both f and h map E(n) to Complex and satisfy MemLp with exponent two. Their classes [f] and [h] "
                    + "are hf.toLp f and hh.toLp h in the actual L2 space. The direction b is an arbitrary element of E(n).")),
                Paragraph(Text("T(n) consists of every real-valued smooth compactly supported test function on E(n), with "
                    + "ContDiff Real (WithTop.some ENat.top) and HasCompactSupport. D(p,x,b) denotes fderiv Real p x applied to b. "
                    + "All real test values and directional derivatives in the integrals are cast to Complex. "
                    + "V(b,t)[f] is DomAddAct.mk (t scalar-multiplied by b) acting on [f]; its representative is x mapping to f(x+t*b). "
                    + "HasDerivAt is the norm derivative with real time.")),
                Paragraph(Text("A compact enlargement of the support of the test derivative gives a uniform integrable bound "
                    + "for translated test pairings. Scalar FTC and the interval-integral identity for continuous linear maps "
                    + "then identify V(b,t)[f]-[f] with the L2 integral of V(b,r)[h] from zero to t. Compact-test separation "
                    + "proves this vector identity, and vector FTC proves the forward implication. Pairing derivatives "
                    + "and derivative uniqueness prove the converse.")),
                Paragraph(Text("Neither global integrability nor derivatives in other directions are required. The dimension n "
                    + "may be zero and the direction b may be zero. The same equivalence retains these cases."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), f = F.Id("f"), h = F.Id("h"), p = F.Id("p"), t = F.Id("t"), x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula euclidean = Call("E", n);
        Formula function = new Formula.TypeArrow(euclidean, complex);
        Formula weak = All([Bound("p", Call("T", n))],
            Equal(Integral(Mul(Call("D", p, x, b), Apply(f, x)), euclidean),
                Seq(Minus, Integral(Mul(Apply(p, x), Apply(h, x)), euclidean))));
        Formula orbit = Seq(Open, t, Colon, Sp, real, Sp, Mapsto, Sp,
            Call("V", b, t, Bracket(f)), Close);
        Formula strong = Call("HasDerivAt", orbit, Bracket(h), D(0));
        Formula hypotheses = new Formula.Logic(
            Call("MemLp", f, D(2), new Formula.NamedConstant(FormulaIdentifier.Create("volume"))), FormulaLogicOperator.And,
            Call("MemLp", h, D(2), new Formula.NamedConstant(FormulaIdentifier.Create("volume"))));
        return All([Bound("n", natural), Bound("b", euclidean), Bound("f", function), Bound("h", function)],
            new Formula.Logic(Parenthesized(hypotheses), FormulaLogicOperator.Implies,
                Parenthesized(new Formula.Logic(weak, FormulaLogicOperator.Iff, strong))));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, Formula value) => new Formula.Apply(function, [value]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Bracket(Formula f) => Seq(OpenBracket, f, CloseBracket);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Integral(Formula expression, Formula euclidean) => Seq(Int, Underscore,
        Grp(F.Id("x"), Colon, Sp, euclidean), Sp, expression, Sp, F.Id("dx"));
}
