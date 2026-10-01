using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class QuditSwappingProductBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/starke2025swapping");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The improved product bound for entanglement swapping conjectured by Starke, Basso, Celeri and Maziero fails for two identical partially entangled ququarts: the average is 723/625, whereas the proposed bound is 507/625.",
        H("A four-dimensional counterexample to the improved swapping bound"),
        Blocks(
            Node("omega", "Bell phase", OmegaFormula(), "The generalized Bell basis uses omega = exp(2 pi i / d). The imaginary unit is i; the natural dimension is cast to a real number in the quotient.", "omega", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phi", "Unnormalized conditional state", PhiFormula(),
                Paragraph(Text(@"Page 5, Eq. (30): `\ket{\phi_{pq}^{AB}} = \frac{1}{\sqrt{d}}\sum_{k=0}^{d-1}c_{p\oplus k} d_k \bar{\omega}^{qk}|p\oplus k,k\rangle`. The paper's d_k is renamed b_k. Indices are ZMod d, p plus k is addition modulo d, and val selects the representative in 0,...,d-1 for the natural exponent. The ket is its computational-basis delta function: ite(P,a,b) is a if P holds and b otherwise. All real scalars in complex arithmetic are cast to C. Translation k to p+k is a bijection, so the post-measurement state is in Schmidt form with sigma(k)=p+k.")),
                "phi", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("norm", "Hilbert norm", NormFormula(), "In the orthonormal computational basis ZMod d times ZMod d, the Hilbert norm is the square root of the sum of squared coordinate moduli. This is the norm used to normalize each conditional state.", "stateNorm", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("prob", "Bell-outcome probability", ProbFormula(),
                Paragraph(Text(@"Page 5, Eq. (31): `\left\Vert\ket{\phi_{pq}^{AB}}\right\Vert^2 = \frac{1}{d}\sum_{k=0}^{d-1}|c_{p\oplus k}|^2 |d_k|^2 = \Pr\big(\Phi_{pq}^{CC'}\big)`. The definition is the squared Hilbert norm of the conditional state, with d_k renamed b_k.")),
                "prob", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("el", "Entanglement in Schmidt form", ElFormula(),
                Paragraph(Text(@"Page 4, Eq. (24): `E_{l_1}(|\xi\rangle_{AC}) = \sum_{j\ne k}|c_j c_k|`. For a normalized state in Schmidt form sum_k a_k |sigma(k),k>, with sigma a bijection, this is the sum over ordered pairs of distinct indices of the modulus of a_j a_k. No division by d-1 is included in El1.")),
                "El1", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("average", "Average post-measurement entanglement", AverageFormula(),
                Paragraph(Text(@"Page 5, Eq. (41): `\big\langle E_{l_1}\big(|\hat{\phi}_{pq}^{AB} \rangle\big) \big\rangle = \sum_{p,q = 0}^{d-1} \Pr\big(\Phi_{pq}^{CC'}\big) E_{l_1}\big( |\hat{\phi}_{pq}^{AB} \rangle \big)`. Each conditional state is divided by its Hilbert norm. Its Schmidt coefficients are the coordinates at (p+k,k); zero-probability outcomes contribute zero. The sum includes all d squared Bell outcomes.")),
                "averageEl1", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The improved upper-bound conjecture", ClaimFormula(),
                Paragraph(Text(@"Page 8, Eq. (59), verbatim (the source formula is quoted in TeX): ""Therefore, we conjecture that the improved upper bound has the form `\big\langle E_{l_1}\big(|\hat{\phi}_{pq}^{AB} \rangle\big) \big\rangle \le \frac{E_{l_1}(|\xi\rangle_{AC}) E_{l_1}(|\eta\rangle_{C'B})}{d-1}.`"" The quantified encoding ranges over every dimension d at least 2 and every pair c,b of normalized complex coefficient vectors. NeZero d supplies the finite ZMod d index type and follows from d at least 2. The paper's second vector d_k is b_k. The denominator is real d minus 1.")),
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The bound fails in dimension four", Disp(new Formula.Not(F.Id("claim"))),
                "Take d=4 and c=b=(7/10,1/10,7/10,1/10). Both sums of squared moduli are 1 and both El1 values are 39/25. For arbitrary positive dimension, the phase has modulus 1 and the weighted entanglement of an outcome is (1/d) times the ordered off-diagonal sum of |c_(p+j)c_(p+k)b_j b_k|. In the zero-probability case, every supported coefficient vanishes; otherwise the squared normalizing factor cancels the probability. Summing over q removes the factor 1/d. Evaluating the resulting correlation sum at these inputs gives 723/625, strictly greater than (39/25)^2/3=507/625.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Node(id, title, formula, Paragraph(Text(prose)), declaration, role, provenance, resolution);

    private static DocumentBlock Node(string id, string title, Formula formula, DocumentBlock prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("quditswap-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(prose), role, resolution);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula f, Formula arg) => new Formula.Apply(f, [arg]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula NeZero(Formula d, Formula body) =>
        Seq(OpenBracket, Call("NeZero", d), CloseBracket, Comma, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Sp, Colon, Sp, type));
    private static Formula Root(Formula a) => Seq(Sqrt, Grp(a));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Z(Formula d) => Call("ZMod", d);
    private static Formula Vectors(Formula d) => Parenthesized(Seq(Z(d), Sp, To, Sp, Complexes()));
    private static Formula Pairs(Formula d) => Parenthesized(Seq(Z(d), Sp, F.Times, Sp, Z(d)));
    private static Formula States(Formula d) => Parenthesized(Seq(Pairs(d), Sp, To, Sp, Complexes()));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula SumOver(Formula k, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, type)), Sp, body);
    private static Formula Inputs(Formula body) => All("d", Nats(), NeZero(F.Id("d"),
        All("c", Vectors(F.Id("d")), All("b", Vectors(F.Id("d")), body))));
    private static Formula Outcomes(Formula body) => All("p", Z(F.Id("d")), All("q", Z(F.Id("d")), body));

    private static Formula OmegaFormula()
    {
        Formula d = F.Id("d");
        return Disp(All("d", Nats(), Eq(Call("omega", d), Call("exp",
            Mul(Cast(new Formula.Fraction(Mul(D(2), Pi), Cast(d, Reals())), Complexes()), F.Id("i"))))));
    }

    private static Formula PhiFormula()
    {
        Formula d = F.Id("d"), c = F.Id("c"), b = F.Id("b"), p = F.Id("p"), q = F.Id("q"), x = F.Id("x"), k = F.Id("k");
        Formula phase = Pow(Call("star", Call("omega", d)), Mul(Call("val", q), Call("val", k)));
        Formula term = Mul(Mul(Mul(Apply(c, Add(p, k)), Apply(b, k)), phase), Call("ite", Eq(x, Pair(Add(p, k), k)), D(1), D(0)));
        Formula value = Mul(new Formula.Fraction(D(1), Cast(Root(Cast(d, Reals())), Complexes())),
            Parenthesized(SumOver(k, Z(d), term)));
        return Disp(Inputs(Outcomes(All("x", Pairs(d), Eq(Call("phi", d, c, b, p, q, x), value)))));
    }

    private static Formula NormFormula()
    {
        Formula d = F.Id("d"), v = F.Id("v"), x = F.Id("x");
        return Disp(All("d", Nats(), NeZero(d, All("v", States(d),
            Eq(Call("stateNorm", d, v), Root(SumOver(x, Pairs(d), Pow(new Formula.Norm(Apply(v, x)), D(2)))))))));
    }

    private static Formula ProbFormula()
    {
        Formula d = F.Id("d"), c = F.Id("c"), b = F.Id("b"), p = F.Id("p"), q = F.Id("q");
        return Disp(Inputs(Outcomes(Eq(Call("prob", d, c, b, p, q),
            Pow(Call("stateNorm", d, Call("phi", d, c, b, p, q)), D(2))))));
    }

    private static Formula ElFormula()
    {
        Formula d = F.Id("d"), a = F.Id("a"), j = F.Id("j"), k = F.Id("k");
        Formula value = SumOver(j, Z(d), SumOver(k, Z(d),
            Call("ite", Eq(j, k), D(0), new Formula.Norm(Mul(Apply(a, j), Apply(a, k))))));
        return Disp(All("d", Nats(), NeZero(d, All("a", Vectors(d), Eq(Call("El1", d, a), value)))));
    }

    private static Formula AverageFormula()
    {
        Formula d = F.Id("d"), c = F.Id("c"), b = F.Id("b"), p = F.Id("p"), q = F.Id("q"), k = F.Id("k");
        Formula probability = Call("prob", d, c, b, p, q);
        Formula norm = Call("stateNorm", d, Call("phi", d, c, b, p, q));
        Formula coefficient = new Formula.Fraction(Call("phi", d, c, b, p, q, Pair(Add(p, k), k)), Cast(norm, Complexes()));
        Formula coefficients = Parenthesized(Seq(k, Sp, Colon, Sp, Z(d), Sp, Mapsto, Sp, coefficient));
        Formula outcome = Call("ite", Eq(probability, D(0)), D(0), Mul(probability, Call("El1", d, coefficients)));
        return Disp(Inputs(Eq(Call("averageEl1", d, c, b), SumOver(p, Z(d), SumOver(q, Z(d), outcome)))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), c = F.Id("c"), b = F.Id("b"), j = F.Id("j"), k = F.Id("k");
        Formula dimension = Rel(D(2), FormulaRelationOperator.LessThanOrEqual, d);
        Formula cunit = Eq(SumOver(j, Z(d), Pow(new Formula.Norm(Apply(c, j)), D(2))), D(1));
        Formula bunit = Eq(SumOver(k, Z(d), Pow(new Formula.Norm(Apply(b, k)), D(2))), D(1));
        Formula bound = Rel(Call("averageEl1", d, c, b), FormulaRelationOperator.LessThanOrEqual,
            new Formula.Fraction(Mul(Call("El1", d, c), Call("El1", d, b)), Sub(Cast(d, Reals()), D(1))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Parenthesized(Inputs(Imp(dimension, Imp(cunit, Imp(bunit, bound)))))));
    }
}
