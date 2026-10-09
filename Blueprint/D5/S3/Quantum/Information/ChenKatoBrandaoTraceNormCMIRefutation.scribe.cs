using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ChenKatoBrandaoTraceNormCMIRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/chen2020mpdoparent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local trace-norm contraction and trace-norm conditional mutual information define a proposed uniform data-processing inequality for finite Kraus channels.",
        H("Trace-norm CMI contraction conjecture"),
        Blocks(
            Node("localContraction", "Local trace-norm contraction ratio", LocalContractionFormula(),
                "Conjecture III.2, PDF p. 17: the local contraction ratio is the supremum of the trace-norm output difference divided by the trace-norm input difference. The two input DensityState values are distinct. Their underlying matrices are exposed by CStarMatrix.ofMatrix.symm. ofKraus(K,K,X) denotes FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus applied to K, K and X, namely the sum of K_i X K_i adjoint. The definition uses the repository traceNorm and the real supremum sSup.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("I1", "Trace-norm conditional mutual information", I1Formula(),
                "Definition 2, PDF p. 14, verbatim: I_1(A:C|B) := ||rho_ABC - rho_A tensor rho_BC||_1 - ||rho_AB - rho_A tensor rho_B||_1. The input coordinates are (A times B) times C. partialTraceRight traces the right factor; partialTraceLeft traces the left factor. The maps R and S reassociate the product indices in opposite directions. AB, A, B and BC are the literal reduced matrices. The tensor product A tensor BC is reassociated back to the input coordinates before subtraction. No rank condition is imposed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Chen–Kato–Brandão Conjecture III.2", ClaimFormula(),
                "Conjecture III.2, PDF p. 17, verbatim: For any channel E: C to CPrime with local contraction ratio eta_1,C < 1, there exists a global constant eta < 1 such that for any tripartite system ABC and any state rho_ABC, I_1(A:CPrime|B)_E(rho) <= eta I_1(A:C|B)_rho. All dimensions range over natural numbers. The finite Kraus family is arbitrary and its completeness equation is the channel hypothesis. L_i is the literal identity on AB kronecker K_i, and the bound applies uniformly to every DensityState on the input product carrier, including singular states.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("ckb-trace-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name)
    {
        string[] words = name.Split('.');
        Formula[] items = new Formula[words.Length * 2 - 1];
        for (int i = 0; i < words.Length; i++)
        {
            items[2 * i] = F.Id(words[i]);
            if (i + 1 < words.Length) items[2 * i + 1] = Dot;
        }
        return Seq(Operatorname, Grp(items));
    }

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula MatrixOf(Formula rows, Formula cols) => Call("Matrix", rows, cols, Complexes);
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinOf(Formula d) => Call("Fin", d);
    private static Formula SumOver(Formula i, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(i, Colon, type), Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula x, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(x, Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula LetIn(Formula x, Formula type, Formula value, Formula body) =>
        Seq(Named("let"), Sp, x, Colon, type, Sp, Colon, Eq, Sp, value, Comma, Sp, body);

    private static Formula LocalContractionFormula()
    {
        Formula n = F.Id("n"), np = F.Id("nPrime"), iota = F.Id("iota"), k = F.Id("K"),
            rho = F.Id("rho"), rhop = F.Id("rhoPrime"), r = F.Id("r");
        Formula x = Call("CStarMatrix.ofMatrix.symm", Call("val", rho));
        Formula xp = Call("CStarMatrix.ofMatrix.symm", Call("val", rhop));
        Formula ratio = Div(Call("traceNorm", Sub(Call("ofKraus", k, k, x),
            Call("ofKraus", k, k, xp))), Call("traceNorm", Sub(x, xp)));
        Formula predicate = Some("rho", Call("DensityState", FinOf(n)),
            Some("rhoPrime", Call("DensityState", FinOf(n)),
                And(new Formula.Not(Equal(rho, rhop)), Equal(r, ratio))));
        Formula set = Seq(OpenBrace, r, Colon, Reals, Sp, Mid, Sp, predicate, CloseBrace);
        Formula body = All("K", new Formula.TypeArrow(iota, MatrixOf(FinOf(np), FinOf(n))),
            Equal(Call("localContraction", k), Call("sSup", set)));
        return Disp(All("n", Naturals, All("nPrime", Naturals, All("iota", Named("Type"),
            Seq(OpenBracket, Call("Fintype", iota), CloseBracket, Sp, body)))));
    }

    private static Formula I1Formula()
    {
        Formula da = F.Id("dA"), db = F.Id("dB"), n = F.Id("n"), m = F.Id("M"),
            ab = F.Id("AB"), a = F.Id("A"), b = F.Id("B"), bc = F.Id("BC"),
            r = F.Id("R"), s = F.Id("S"), p = F.Id("p");
        Formula aa = FinOf(da), bb = FinOf(db), cc = FinOf(n);
        Formula abc = Product(Product(aa, bb), cc), regrouped = Product(aa, Product(bb, cc));
        Formula right = LambdaOf(p, regrouped, Pair(Pair(Call("Prod.fst", p),
            Call("Prod.fst", Call("Prod.snd", p))), Call("Prod.snd", Call("Prod.snd", p))));
        Formula left = LambdaOf(p, abc, Pair(Call("Prod.fst", Call("Prod.fst", p)),
            Pair(Call("Prod.snd", Call("Prod.fst", p)), Call("Prod.snd", p))));
        Formula value = Sub(Call("traceNorm", Sub(m,
            Call("Matrix.submatrix", Call("Matrix.kronecker", a, bc), s, s))),
            Call("traceNorm", Sub(ab, Call("Matrix.kronecker", a, b))));
        Formula body = LetIn(r, new Formula.TypeArrow(regrouped, abc), right,
            LetIn(s, new Formula.TypeArrow(abc, regrouped), left,
            LetIn(ab, MatrixOf(Product(aa, bb), Product(aa, bb)), Call("partialTraceRight", m),
            LetIn(a, MatrixOf(aa, aa), Call("partialTraceRight", ab),
            LetIn(b, MatrixOf(bb, bb), Call("partialTraceLeft", ab),
            LetIn(bc, MatrixOf(Product(bb, cc), Product(bb, cc)),
                Call("partialTraceLeft", Call("Matrix.submatrix", m, r, r)),
                Equal(Call("I1", m), value)))))));
        return Disp(All("dA", Naturals, All("dB", Naturals, All("n", Naturals,
            All("M", MatrixOf(abc, abc), body)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), np = F.Id("nPrime"), iota = F.Id("iota"), k = F.Id("K"),
            i = F.Id("i"), eta = F.Id("eta"), da = F.Id("dA"), db = F.Id("dB"),
            rho = F.Id("rho"), l = F.Id("L");
        Formula ab = Product(FinOf(da), FinOf(db));
        Formula abc = Product(ab, FinOf(n));
        Formula x = Call("CStarMatrix.ofMatrix.symm", Call("val", rho));
        Formula lifted = LambdaOf(i, iota, Call("Matrix.kronecker",
            Parenthesized(Seq(D(1), Colon, MatrixOf(ab, ab))), Apply(k, i)));
        Formula bound = LetIn(l, new Formula.TypeArrow(iota, MatrixOf(Product(ab, FinOf(np)), abc)), lifted,
            LeqTo(Call("I1", Call("ofKraus", l, l, x)), Mul(eta, Call("I1", x))));
        Formula states = All("dA", Naturals, All("dB", Naturals,
            All("rho", Call("DensityState", abc), bound)));
        Formula contraction = Some("eta", Reals, And(Less(eta, D(1)), states));
        Formula hypothesis = Imp(Equal(SumOver(i, iota,
                Mul(Call("conjTranspose", Apply(k, i)), Apply(k, i))), D(1)),
            Imp(Less(Call("localContraction", k), D(1)), contraction));
        Formula body = All("n", Naturals, All("nPrime", Naturals, All("iota", Named("Type"),
            Seq(OpenBracket, Call("Fintype", iota), CloseBracket, Sp,
                All("K", new Formula.TypeArrow(iota, MatrixOf(FinOf(np), FinOf(n))), hypothesis)))));
        return Disp(IffTo(F.Id("claim"), body));
    }
}
