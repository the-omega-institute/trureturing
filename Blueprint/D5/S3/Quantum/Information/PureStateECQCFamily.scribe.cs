using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class PureStateECQCFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/PureStateECQCFamily.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In every prime dimension p congruent to one modulo four, a maximally entangled pure state has ln p mutual information in every Clifford basis and exceeds the ECQC budget by (p−2) ln p.",
        H("The prime-dimensional pure-state ECQC failure family"),
        Blocks(
            Node("bases", "The computational and quadratic-phase columns", BasesFormula(),
                "Option (ZMod p) indexes the p+1 bases: none denotes the computational basis and some a denotes the quadratic basis a. The column and coordinate are b and x. Pi.single(b,1,x) is the computational column. stdAddChar(z) = exp(2πiz/p), with arithmetic in ZMod p. The denominator is sqrt(p), embedded in the complex numbers. These are the complete Clifford MUB columns of Ivanović (1981, DOI 10.1088/0305-4470/14/12/019) and Wootters–Fields (1989, DOI 10.1016/0003-4916(89)90322-9).", DescribeRole.Definition),
            Node("jointLaw", "The same-basis Born law", JointFormula(),
                "Both parties measure the same indexed column basis. The amplitude conjugates both measured columns and sums over the two state coordinates. normSq is the squared complex modulus. The second measurement basis is the same column family as the first. fst and snd select the two coordinates of a pair.", DescribeRole.Definition),
            Node("claim", "Pure-state ECQC in dimension p", ClaimFormula(),
                "The assertion ranges over all normalized pure amplitudes. The minimum is the infimum of all sums over p-element subsets of the p+1 measurement indices. This finite set is nonempty. The existing mutualInformation and quantumMutualInformation use natural logarithms, and pureDensityState is the positive trace-one rank-one projector with its actual partial-trace marginals. This is the pure-state restriction of Iqbal's ECQC assertion (arXiv:2509.08286v2, labelled Conjecture 3.1 in that version and cited as Conjecture 2.1).", DescribeRole.Definition),
            Node("result", "A uniform failure family", ResultFormula(),
                "A prime p congruent to one modulo four admits a square root u of −1. For every such u, take the amplitude psi(x,y) = 1/sqrt(p) on y = ux and zero elsewhere. In each quadratic basis the two quadratic phases cancel because 1+u² = 0. Primitive additive-character orthogonality gives the amplitude 1/sqrt(p) precisely on c = ub, as in the computational basis. Each Born law is uniform on this bijection graph; its two marginal entropies and joint entropy equal ln p, giving classical mutual information ln p. Both partial traces are I/p and the global rank-one entropy vanishes, giving quantum mutual information 2 ln p. Every p-element information sum is p ln p, so the exact excess is (p−2) ln p > 0. Appleby's extended-Clifford formulas (arXiv:0909.5233, equations 76, 77 and 219) supply the cited intermediate basis symmetry: the antiunitary associated with uI fixes each MUB and permutes its columns. The dimension-five case is the existing PureStateECQCRefutation result; the formula here holds uniformly in p.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("ecqcf-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(
        Seq(Operatorname, Grp(name.Split('.').SelectMany((part, index) => index == 0
            ? new[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) }).ToArray())), [.. args]);
    private static Formula All(Formula v, Formula type, Formula body) =>
        Seq(Forall, Sp, v, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula v, Formula type, Formula body) =>
        Seq(Exists, Sp, v, Colon, Sp, type, Comma, Sp, body);
    private static Formula EqTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula LeTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula LtTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Inv(Formula x) => new Formula.Power(Par(x), Seq(Minus, D(1)));
    private static Formula Negate(Formula x) => Seq(Minus, Par(x));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Conj(params Formula[] terms) => terms.Reverse().Aggregate((rest, term) => And(term, rest));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Lambda(Formula v, Formula type, Formula body) => Seq(v, Colon, Sp, type, Mapsto, Sp, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Field(Formula p) => Call("ZMod", p);
    private static Formula Indices(Formula p) => Call("Option", Field(p));
    private static Formula PairType(Formula p) => Par(Seq(Field(p), Times, Field(p)));
    private static Formula Amplitudes(Formula p) => Seq(PairType(p), To, Sp, Complexes());
    private static Formula Cast(Formula x, Formula type) => Par(Seq(x, Colon, Sp, type));
    private static Formula WithInstance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula ForP(Formula p, Formula body) => All(p, Nats(), WithInstance(Call("NeZero", p), body));
    private static Formula SumOf(Formula v, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(v, InMacro, Sp, domain)), Sp, body);
    private static Formula Basis(Formula p, Formula i, Formula b, Formula x) => Call("bases", p, i, b, x);
    private static Formula Law(Formula p, Formula i, Formula psi) => Call("jointLaw", p, i, psi);
    private static Formula MI(Formula p, Formula i, Formula psi) => Call("mutualInformation", Law(p, i, psi));
    private static Formula QMI(Formula psi, Formula hpsi) =>
        Call("quantumMutualInformation", Call("pureDensityState", psi, hpsi));
    private static Formula Normalize(Formula psi) => EqTo(Call("dotProduct", Call("star", psi), psi), D(1));
    private static Formula Log(Formula p) => Call("Real.log", p);
    private static Formula Sums(Formula p, Formula psi)
    {
        Formula r = F.Id("r"), s = F.Id("S"), i = F.Id("i");
        var predicate = Some(s, Call("Finset", Indices(p)),
            And(EqTo(Call("card", s), p), EqTo(r, SumOf(i, s, MI(p, i, psi)))));
        return Seq(OpenBrace, r, Colon, Sp, Reals(), Bar, Par(predicate), CloseBrace);
    }

    private static Formula BasesFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b"), x = F.Id("x");
        var computational = All(b, Field(p), All(x, Field(p),
            EqTo(Basis(p, F.Id("none"), b, x), Call("Pi.single", b, Cast(D(1), Complexes()), x))));
        var phase = Add(Mul(a, new Formula.Power(x, D(2))), Mul(b, x));
        var quadratic = All(a, Field(p), All(b, Field(p), All(x, Field(p),
            EqTo(Basis(p, Call("some", a), b, x),
                new Formula.Fraction(Call("stdAddChar", phase), Cast(Call("Real.sqrt", p), Complexes()))))));
        return Disp(ForP(p, And(computational, quadratic)));
    }

    private static Formula JointFormula()
    {
        Formula p = F.Id("p"), i = F.Id("i"), psi = F.Id("psi"), bc = F.Id("bc"), xy = F.Id("xy");
        var summand = Mul(Mul(Call("star", Basis(p, i, Call("fst", bc), Call("fst", xy))),
            Call("star", Basis(p, i, Call("snd", bc), Call("snd", xy)))), new Formula.Apply(psi, [xy]));
        return Disp(ForP(p, All(i, Indices(p), All(psi, Amplitudes(p), All(bc, PairType(p),
            EqTo(Call("jointLaw", p, i, psi, bc), Call("normSq", SumOf(xy, PairType(p), summand))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p"), psi = F.Id("psi"), hp = F.Id("hpsi");
        var assertion = All(psi, Amplitudes(p), All(hp, Par(Normalize(psi)),
            LeTo(Call("sInf", Sums(p, psi)), QMI(psi, hp))));
        return Disp(ForP(p, new Formula.Logic(Call("claim", p), FormulaLogicOperator.Iff, Par(assertion))));
    }

    private static Formula ResultFormula()
    {
        Formula p = F.Id("p"), u = F.Id("u"), psi = F.Id("psi"), hpsi = F.Id("hpsi"),
            i = F.Id("i"), bc = F.Id("bc"), xy = F.Id("xy"), z = F.Id("z");
        var root = EqTo(new Formula.Power(u, D(2)), Seq(Minus, D(1)));
        var state = Lambda(xy, PairType(p), Call("ite",
            EqTo(Call("snd", xy), Mul(u, Call("fst", xy))), Inv(Cast(Call("Real.sqrt", p), Complexes())), D(0)));
        var graph = All(i, Indices(p), All(bc, PairType(p), EqTo(Call("jointLaw", p, i, psi, bc),
            Call("ite", EqTo(Call("snd", bc), Mul(u, Call("fst", bc))), Inv(Cast(p, Reals())), D(0)))));
        var uniform = Lambda(z, Field(p), Inv(Cast(p, Reals())));
        var left = All(i, Indices(p), EqTo(Call("ChainRule.marginal", Law(p, i, psi)), uniform));
        var swapped = Lambda(bc, PairType(p), Call("jointLaw", p, i, psi,
            Par(Seq(Call("snd", bc), Comma, Call("fst", bc)))));
        var right = All(i, Indices(p), EqTo(Call("ChainRule.marginal", swapped), uniform));
        var excess = Mul(Sub(Cast(p, Reals()), D(2)), Log(p));
        var conclusions = Conj(graph, left, right, All(i, Indices(p), EqTo(MI(p, i, psi), Log(p))),
            EqTo(QMI(psi, hpsi), Mul(D(2), Log(p))),
            EqTo(Sub(Call("sInf", Sums(p, psi)), QMI(psi, hpsi)), excess),
            LtTo(D(0), excess), new Formula.Not(Call("claim", p)));
        var everyRoot = All(u, Field(p), Imp(root,
            Seq(Operatorname, Grp(F.Id("let")), Sp, psi, Colon, Sp, Amplitudes(p), Colon, Eq, Sp,
                Par(state), Semi, Sp, Some(hpsi, Par(Normalize(psi)), conclusions))));
        var body = Imp(EqTo(new Formula.Modulo(p, D(4)), D(1)),
            And(Some(u, Field(p), root), everyRoot));
        return Disp(All(p, Nats(), WithInstance(Call("Fact", Call("Nat.Prime", p)), body)));
    }
}
