using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class GuoJinMaxMarginalEntropyLOCCDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/guojin2025measure");
    private const string Conjecture = "Page 88, Section 9.4: “Note here that we can not prove here E′^(n) is nonincreasing on average under LOCC, but we conjecture that E′^(n) does not increase on average under LOCC for these cases mentioned above. Hereafter we always assume the conjecture is true.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A local measurement on a four-party pure state increases the average maximum single-party entropy.",
        H("Maximum marginal entropy can increase under a local measurement"),
        Blocks(
            Node("marginal", "The one-party reduced matrix", MarginalFormula(),
                "The amplitude function is indexed by basis tuples Fin n → Fin d. The matrix entry sums ψ(x) times the conjugate of ψ(x[i ↦ b]) over tuples with x(i) = a. This is the reduced density matrix of party i for a normalized pure state.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("maxMarginalEntropy", "The largest single-party entropy", MaximumFormula(),
                "Pages 87–88, Eq. (189): “The quantity E′^(n)(|ψ⟩) = max_i h(ρ^{A_i}) can reports the amount of entanglement contained in |ψ⟩ to some extent [168]: If it is nonincreasing on average under LOCC, then (i) E′^(3) is a complete global MEM but not tightly complete monogamous, and if h is strictly concave, E′^(3) is completely monogamous, and (ii) E′^(n) is not complete whenever n ≥ 4.” Table 16 includes h = S. Page 14, Section 2: “S(ρ) = −Tr(ρ log₂ ρ) is the von Neumann entropy of the state ρ”. CFC.log is the operator logarithm on CStarMatrix; division by Real.log 2 gives entropy in bits. The expression is defined on all matrices and represents entropy for positive trace-one matrices. The real iSup over Fin n represents this maximum for a nonempty finite collection of parties.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("applyLocal", "A local Kraus operator on amplitudes", LocalFormula(),
                "K acts on the i-th coordinate of a basis tuple. Its row x(i) is contracted with the amplitudes obtained by replacing that coordinate with a. All other coordinates stay fixed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed average monotonicity", Equal(Named("claim"), ClaimBody()),
                Conjecture + " Here n counts parties, d is their common local dimension, and m counts measurement outcomes. The input has squared norm one. The Kraus operators obey ∑ᵣ Kᵣ†Kᵣ = 1. A branch has probability equal to its squared norm, is normalized by the inverse square root of that probability, and contributes zero when the probability is zero. The formula states the consequence for one local measurement.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A four-party counterexample", new Formula.Not(Parenthesized(ClaimBody())),
                "Take four parties of local dimension nine. The pure amplitude is 1/4 on the sixteen tuples (0,0,j,j) and (j,j,0,0), with j = 1,…,8, and zero elsewhere. Every initial marginal is diagonal with entries 1/2,1/16,…,1/16, so its entropy is 5/2. On party zero, the projectors Matrix.diagonal (Pi.single 0 1) and its complement give two branches of probability 1/2. In the first normalized branch, party two has diagonal marginal (0,1/8,…,1/8); in the second, party zero has that marginal. Each outcome maximum is therefore at least 3, and their average exceeds 5/2. The maximizing party can depend on the outcome. The theorem does not assert an upper bound on either outcome maximum or settle the three-party case.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("guojin-" + (name switch { "maxMarginalEntropy" => "maximum", "applyLocal" => "local", _ => name })),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name)
    {
        string[] parts = name.Split('.');
        Formula[] items = new Formula[2 * parts.Length - 1];
        for (int i = 0; i < parts.Length; i++)
        {
            items[2 * i] = F.Id(parts[i]);
            if (i + 1 < parts.Length) items[2 * i + 1] = Dot;
        }
        return Seq(Operatorname, Grp(items));
    }
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula State(Formula n, Formula d) => Arrow(Arrow(Fin(n), Fin(d)), Complexes);
    private static Formula Matrix(Formula d) => Call("Matrix", Fin(d), Fin(d), Complexes);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula All(string v, Formula t, Formula b) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), t, b);
    private static Formula Lambda(string v, Formula t, Formula b) => Seq(
        Operatorname, Grp(F.Id("fun")), Sp, Typed(F.Id(v), t), Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula SumOver(string v, Formula t, Formula b) => Seq(
        new Formula.Subscript(Sum, Seq(F.Id(v), Colon, Sp, t)), Sp, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Inverse(Formula a) => new Formula.Power(Parenthesized(a), new Formula.Negate(D(1)));
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Max(Formula state) => Call("maxMarginalEntropy", state);

    private static Formula MarginalFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), psi = F.Id("psi"), i = F.Id("i");
        Formula x = F.Id("x"), a = F.Id("a"), b = F.Id("b");
        Formula update = Call("Function.update", x, i, b);
        Formula entry = SumOver("x", Arrow(Fin(n), Fin(d)), Ite(
            Equal(App(x, i), a), Mul(App(psi, x), Call("star", App(psi, update))), Typed(D(0), Complexes)));
        return All("n", Naturals, All("d", Naturals, All("psi", State(n, d), All("i", Fin(n),
            Equal(Call("marginal", psi, i), Call("CStarMatrix.ofMatrix",
                Lambda("a", Fin(d), Lambda("b", Fin(d), entry))))))));
    }
    private static Formula MaximumFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), psi = F.Id("psi"), i = F.Id("i");
        return All("n", Naturals, All("d", Naturals, All("psi", State(n, d),
            Equal(Max(psi), Call("iSup", Lambda("i", Fin(n),
                new Formula.Fraction(new Formula.Negate(Call("Complex.re",
                    Call("Matrix.trace", Mul(Call("marginal", psi, i), Call("CFC.log", Call("marginal", psi, i)))))),
                    Call("Real.log", Typed(D(2), Reals)))))))));
    }
    private static Formula LocalFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), k = F.Id("K"), i = F.Id("i"), psi = F.Id("psi");
        Formula x = F.Id("x"), a = F.Id("a");
        Formula value = SumOver("a", Fin(d), Mul(App(k, App(x, i), a),
            App(psi, Call("Function.update", x, i, a))));
        return All("n", Naturals, All("d", Naturals, All("K", Matrix(d), All("i", Fin(n),
            All("psi", State(n, d), Equal(Call("applyLocal", k, i, psi),
                Lambda("x", Arrow(Fin(n), Fin(d)), value)))))));
    }
    private static Formula Mass(Formula n, Formula d, Formula psi) => SumOver("x", Arrow(Fin(n), Fin(d)),
        Call("Complex.normSq", App(psi, F.Id("x"))));
    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), d = F.Id("d"), m = F.Id("m"), psi = F.Id("psi"), i = F.Id("i"), k = F.Id("K"), r = F.Id("r");
        Formula kr = App(k, r);
        Formula branch = Call("applyLocal", kr, i, psi);
        Formula p = Mass(n, d, branch);
        Formula normalized = Call("HSMul.hSMul", Inverse(Call("Complex.ofReal", Call("Real.sqrt", p))), branch);
        Formula complete = Equal(SumOver("r", Fin(m), Mul(Call("Matrix.conjTranspose", kr), kr)), Typed(D(1), Matrix(d)));
        Formula average = SumOver("r", Fin(m), Ite(Equal(p, Typed(D(0), Reals)), Typed(D(0), Reals), Mul(p, Max(normalized))));
        return All("n", Naturals, All("d", Naturals, All("m", Naturals, All("psi", State(n, d), All("i", Fin(n),
            All("K", Arrow(Fin(m), Matrix(d)), Imp(Equal(Mass(n, d, psi), Typed(D(1), Reals)),
                Imp(complete, Leq(average, Max(psi))))))))));
    }
}
