using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class GazeauNormalRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/GazeauNormalRealization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/gazeau2026interlaced");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary Gazeau block action on the full Schwartz core has no closed densely defined self-adjoint, skew-adjoint, or normal realization under any complete positive Hilbert metric on the fixed complex vector space.",
        H("Gazeau's Schwartz action admits no normal Hilbert realization"),
        Blocks(
            Node("embed", "The Lebesgue L2 embedding", EmbedFormula(),
                "ScalarL2 is Lp(C, 2, volume) on the real line, with its usual almost-everywhere equivalence classes. V is ScalarL2 times ScalarL2 and Core is Schwartz(R,C) times Schwartz(R,C). For c = (f,h), embed(c) takes both actual Schwartz functions to their Lebesgue L2 classes. This map is injective.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("expression", "The full first-order source action", ExpressionFormula(),
                "On every Schwartz pair, expression(f,h) = (xf + i h', -i f' + xh). The coordinate multiplication is the genuine complex-linear map f(x) to x f(x), and the primes are real derivatives. The action is defined on all of Core.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sourceGraph", "Algebraic transport of the entire source graph", SourceGraphFormula(),
                "H carries the candidate Hilbert structure and e is any algebraic complex-linear equivalence from V to H. sourceGraph(e) contains the pair (e(embed(c)), e(embed(expression(c)))) for every c in Core. Continuity of e, equivalence to the standard L2 norm, and density of the transported Schwartz core are not assumed.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "All three adjoint alternatives are impossible", ResultFormula(),
                "H is any complete complex Hilbert space. The partial operator T is complex-linear, its domain is dense in H, and its graph is closed in H times H. The expression adjoint(T) is its actual Hilbert adjoint, denoted Tstar in the explanation. Each existential intermediate vector below imposes the appropriate product domain, so the displayed relation equality is the full maximal-graph equality Tstar after T = T after Tstar. Equality Tstar = T or Tstar = -T includes equality of domains.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gazeau-2026-problem-4-3-hilbert-realization"),
                    ResolutionKind.Refuted)),
            Paragraph(Text("Take the actual Schwartz Gaussian g(x) = exp(-x squared / 2). Its derivative is -xg, and (xg)' = g - x squared g. Thus the core pairs cv = (g,-ig) and cw = (xg,-ixg) satisfy expression(cv) = 0 and expression(cw) = cv. The vector v = e(embed(cv)) is nonzero since g(0) = 1 and both embeddings are injective. Full source graph containment gives Tv = 0 and Tw = v.")),
            Paragraph(Text("In the normal branch, product-graph equality at (v,0) supplies Tstar v = a with a in the domain of T and Ta = 0. The actual adjoint identity gives inner(a,a) = inner(v,Ta) = 0, hence a = 0. Applying the identity at w gives inner(v,v) = inner(a,w) = 0, a contradiction. In the self-adjoint and skew-adjoint branches, the partial-map equality directly gives Tstar v = 0 and the same contradiction.")),
            Paragraph(Text("Every complete positive Hermitian metric on the fixed vector space V is represented by a type copy H and an algebraic equivalence e. A genuine self-adjoint or skew-adjoint graph closure retaining this source action would be such an extension and is therefore excluded. No arbitrary-metric closability or density of the original core is asserted. Problem 4.4, distributional operators, interlaced products and indefinite metrics remain outside this conclusion.")))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("gazeau-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Id(string value) => F.Id(value);
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. arguments]);
    private static Formula Pair(Formula first, Formula second) => Seq(Open, first, Comma, Sp, second, Close);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.And, P(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.Or, P(right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Graph(Formula op) => Call("graph", op);
    private static Formula EmbedFormula() => Disp(All("f", Call("Schwartz", Id("R"), Id("C")),
        All("h", Call("Schwartz", Id("R"), Id("C")),
            Eq(Call("embed", Pair(Id("f"), Id("h"))),
                Pair(Call("toLp", Id("f"), D(2), Id("volume")),
                     Call("toLp", Id("h"), D(2), Id("volume")))))));
    private static Formula ExpressionFormula() => Disp(All("f", Call("Schwartz", Id("R"), Id("C")),
        All("h", Call("Schwartz", Id("R"), Id("C")),
            Eq(Call("expression", Pair(Id("f"), Id("h"))),
                Pair(Seq(Id("x"), Id("f"), Plus, Id("i"), Id("h"), Apos),
                     Seq(Minus, Id("i"), Id("f"), Apos, Plus, Id("x"), Id("h")))))));
    private static Formula SourceGraphFormula()
    {
        var c = Id("c");
        var image = Pair(Call("e", Call("embed", c)),
            Call("e", Call("embed", Call("expression", c))));
        return Disp(Eq(Call("sourceGraph", Id("e")),
            Seq(OpenBrace, image, Sp, Mid, Sp, Mem(c, Id("Core")), CloseBrace)));
    }
    private static Formula ResultFormula()
    {
        var t = Id("T"); var ts = Call("adjoint", t); var x = Id("x");
        var y = Id("y"); var z = Id("z"); var h = Id("H");
        var left = Some("y", h, And(Mem(Pair(x, y), Graph(t)), Mem(Pair(y, z), Graph(ts))));
        var right = Some("y", h, And(Mem(Pair(x, y), Graph(ts)), Mem(Pair(y, z), Graph(t))));
        var normal = All("x", h, All("z", h,
            new Formula.Logic(P(left), FormulaLogicOperator.Iff, P(right))));
        var alternatives = Or(Eq(ts, t), Or(Eq(ts, Seq(Minus, t)), normal));
        var containment = new Formula.Relation(Call("sourceGraph", Id("e")),
            FormulaRelationOperator.SubsetOf, Graph(t));
        var conditions = And(containment, And(Call("Dense", Call("domain", t)),
            And(Call("IsClosed", t), alternatives)));
        return Disp(All("H", Id("CompleteComplexHilbertSpace"),
            All("e", Call("ComplexLinearEquivalence", Id("V"), h),
                new Formula.Not(Some("T", Call("ComplexLinearPartialOperator", h, h), conditions)))));
    }
}
