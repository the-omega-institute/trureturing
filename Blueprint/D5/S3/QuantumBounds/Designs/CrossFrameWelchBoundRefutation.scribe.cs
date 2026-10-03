using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.Designs;

internal sealed class CrossFrameWelchBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/aceska2022crossframe");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A spanning family of three nonzero vectors in the real plane and its dual have cross-Gramian coherence 3/19, below the proposed Welch bound 1/3.",
        H("A dual-frame counterexample to the cross-Gramian Welch bound"),
        Blocks(
            Node("IsFrame", "Finite-dimensional frames", FrameFormula(),
                "Definition 1 (arXiv:2205.05613v3, p. 3) defines a frame by positive lower and finite upper bounds for the sum of squared analysis coefficients. The source then states verbatim: \"In a finite-dimensional space H, frames are simply spanning sets of H.\" IsFrame uses this characterization: the real linear span of the range of F is the whole Euclidean space. Fin k indexes the k vectors from zero, and EuclideanSpace R (Fin n) is the standard real n-dimensional Hilbert space. The condition k >= n is supplied in claim.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsDualFrame", "Both dual reconstruction equations", DualFormula(),
                "Definition 3 (p. 3): \"Let {f_i}_{i=1}^k be a frame for H. A dual frame for {f_i}_{i=1}^k is a frame {g_i}_{i=1}^k such that for every f ∈ H,\" followed by f = sum_i <f,g_i> f_i = sum_i <f,f_i> g_i. IsDualFrame includes that G is a frame and both equations, with x denoting the source's f. The assumption that F is a frame appears separately in claim. All inner products and scalar multiplications are over R.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coherence", "Maximal off-diagonal magnitude", CoherenceFormula(),
                "Section 4 (p. 12): \"Let F = {f₁, …, fₖ} be a frame for Fⁿ, and let H = {h₁, …, hₖ} be a dual frame for F. We denote the cross-Gramian of F and H by Gr(F, H) and we denote the maximal off-diagonal magnitude of Gr(F, H) as\" followed by µ(Gr(F, H)) := max_{i≠j} |⟨f_i, h_j⟩|. Here G denotes H. coherence is the supremum over the subtype of pairs (i,j) with i ≠ j. For k >= 2 the finite index set is nonempty, so this is precisely the source's maximum. Subtype takes the displayed predicate on pairs; val extracts the underlying pair, and Prod.fst and Prod.snd are its two projections.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 41", ClaimFormula(),
                "Conjecture 41 (Section 4.2, p. 17), verbatim: \"Let F be a frame for Fⁿ, and let G be one of its dual frames. Then\" µ(Gr(F, G)) ≥ √((nk − n²)/(k²(k − 1))). (21) The encoding takes the real case of the source's field R or C. It quantifies all n, k and all vector families F, G, with n <= k and 2 <= k so that the off-diagonal maximum is nonempty. The operator val denotes the natural-to-real cast; every subtraction and the division in the square root are in R.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture is false", Disp(new Formula.Not(F.Id("claim"))),
                "Take n = 2, k = 3 and F = ((-3,-3),(-3,3),(-1,0)), with G = ((-3/19,-1/6),(-3/19,1/6),(-1/19,0)). Both reconstruction equations hold for every x. Each family therefore spans: reconstruction writes every x as a linear combination of its members. The six off-diagonal inner products are -1/38, 3/19, -1/38, 3/19, 3/19, 3/19 in the order (0,1),(0,2),(1,0),(1,2),(2,0),(2,1). Their maximum absolute value is 3/19, strictly below sqrt(1/9) = 1/3. These exact rational computations refute the universally quantified claim.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("aceska-kaczanowski-2022-cross-frame-welch-bound-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("cross-frame-welch-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula IffTo(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Space() => Call("EuclideanSpace", Reals(), Call("Fin", F.Id("n")));
    private static Formula Family() => Seq(Call("Fin", F.Id("k")), Sp, To, Sp, Space());
    private static Formula Inner(Formula left, Formula right) => Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);
    private static Formula Parameters(Formula body, bool includeG) =>
        All("n", Nats(), All("k", Nats(), All("F", Family(),
            includeG ? All("G", Family(), body) : body)));
    private static Formula Reconstruction(string analysis, string synthesis)
    {
        Formula x = F.Id("x"), i = F.Id("i");
        Formula summand = Mul(Inner(x, Call(analysis, i)), Call(synthesis, i));
        return All("x", Space(), EqTo(
            Seq(F.Sum, Underscore, Grp(Seq(i, Colon, Sp, Call("Fin", F.Id("k")))), Sp, summand), x));
    }
    private static Formula FrameFormula() => Disp(Parameters(
        IffTo(Call("IsFrame", F.Id("F")), EqTo(
            Call("span", Reals(), Call("range", F.Id("F"))), Seq(Operatorname, Grp(F.Id("top"))))), false));
    private static Formula DualFormula() => Disp(Parameters(
        IffTo(Call("IsDualFrame", F.Id("F"), F.Id("G")),
            And(Call("IsFrame", F.Id("G")), And(Reconstruction("G", "F"), Reconstruction("F", "G")))), true));
    private static Formula CoherenceFormula()
    {
        Formula First(Formula value) => new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("Prod"), Dot, F.Id("fst"))), [value]);
        Formula Second(Formula value) => new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("Prod"), Dot, F.Id("snd"))), [value]);
        Formula p = F.Id("p"), q = F.Id("q");
        Formula pairs = Seq(Call("Fin", F.Id("k")), Sp, Times, Sp, Call("Fin", F.Id("k")));
        Formula subtype = Call("Subtype", Seq(LambdaLower, Sp, q, Colon, Sp, pairs, Comma, Sp,
            Rel(First(q), FormulaRelationOperator.NotEqual, Second(q))));
        Formula pair = Call("val", p);
        Formula magnitude = new Formula.Absolute(Inner(
            Call("F", First(pair)), Call("G", Second(pair))));
        Formula supremum = Call("iSup", Seq(LambdaLower, Sp, p, Colon, Sp, subtype, Comma, Sp, magnitude));
        return Disp(Parameters(EqTo(Call("coherence", F.Id("F"), F.Id("G")), supremum), true));
    }
    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula nr = Call("val", n), kr = Call("val", k);
        Formula bound = Seq(Sqrt, Grp(new Formula.Fraction(
            Sub(Mul(nr, kr), Square(nr)), Mul(Square(kr), Parenthesized(Sub(kr, D(1)))))));
        Formula conclusion = LeTo(bound, Call("coherence", F.Id("F"), F.Id("G")));
        Formula quantified = Parameters(Implies(LeTo(n, k), Implies(LeTo(D(2), k),
            Implies(Call("IsFrame", F.Id("F")), Implies(Call("IsDualFrame", F.Id("F"), F.Id("G")), conclusion)))), true);
        return Disp(IffTo(F.Id("claim"), quantified));
    }
}
