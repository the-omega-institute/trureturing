using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class BouafiaNegativeTypeDiversityDeletionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/bouafia2026treemagnitude");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-point scaled Hamming metric refutes irreversible diversity-weight deletion.",
        H("Negative type does not justify irreversible deletion"),
        Blocks(
            Entry("negative-type", "NegativeType", "The square-root metric embeds isometrically",
                NegativeTypeFormula(),
                "Bouafia, arXiv:2605.03681v1, p. 4, §2.2, verbatim: “A metric space (X,d) is said to be of negative type if (X,√d) admits an isometric embedding into a Hilbert space.” "
                + "For a finite set Fin n, the image lies in a finite-dimensional real Hilbert space, represented by EuclideanSpace ℝ (Fin m). The formula requires an injective map preserving every square-root distance.",
                DescribeRole.Definition, true),
            Entry("similarity", "similarity", "Exponential similarity", SimilarityFormula(),
                "Bouafia, p. 3, §2.1, defines the similarity kernel by “Z(x,y) = e⁻ᵈ⁽ˣ,ʸ⁾”. The scale is one, and distances are real-valued. The anonymous bracket denotes a MetricSpace instance on Fin n.",
                DescribeRole.Definition, true),
            Entry("weighting", "weighting", "One inverse solve extended by zero", WeightingFormula(),
                "Algorithm 1, p. 16, first sets w to zero on X and then sets its restriction to A to Z restricted to A inverse times the constant-one vector. Matrix.submatrix uses the subtype inclusions. The dot in the constant function is an anonymous argument; hi is the proof that i lies in A.",
                DescribeRole.Definition, true),
            Entry("active", "active", "The sequence of retained supports", ActiveFormula(),
                "Algorithm 1, p. 16, starts with all points and retains exactly the strictly positive coordinates after each solve. Indices k begin at zero, so k=1 denotes the second solve. Removed coordinates have zero extended weight.",
                DescribeRole.Definition, true),
            Entry("stopped", "stopped", "The nonnegative stopping condition", StoppedFormula(),
                "Theorem 4's proof, p. 16, states verbatim: “At the end of the repeat loop, the vector w is non-zero and non-negative.” This is the stopping condition used here. The printed Algorithm 1 instead has the reversed test w ≱ 0. The counterexample uses the nonnegative condition from the proof.",
                DescribeRole.Definition, true),
            Entry("first-stop", "FirstStop", "The first valid nonnegative solve", FirstStopFormula(),
                "Every visited active set is nonempty, and its principal similarity matrix has nonzero determinant. No earlier solve is nonnegative, and the solve at k is nonnegative. These conditions ensure that the total matrix inverse describes a genuine inverse at every visited step.",
                DescribeRole.Definition, false),
            Entry("mass", "mass", "Total weight", MassFormula(),
                "Algorithm 1, p. 16, sums the extended weighting over the original finite set. At a nonzero nonnegative solve this is the positive denominator for the returned probability.",
                DescribeRole.Definition, true),
            Entry("output", "output", "The returned normalized vector", OutputFormula(),
                "Algorithm 1, p. 16, returns the weighting divided by its total mass. The universal assertion below requires this denominator to be positive, in addition to requiring a first stop to exist.",
                DescribeRole.Definition, true),
            Entry("maximizing", "DiversityMaximizing", "Minimum energy over the probability simplex",
                MaximizingFormula(),
                "Bouafia, p. 2, introduction, verbatim: “A probability measure μ : X → [0, 1] is said to be diversity-maximizing if it minimizes the quantity” μᵀ Z μ = ∑ₓ,ᵧ∈X e⁻ᵈ⁽ˣ,ʸ⁾ μ(x)μ(y), “which represents the average similarity between two independent samples drawn according to μ.” "
                + "Convexity.StdSimplex represents precisely the nonnegative finite probabilities of total mass one. Both the feasibility conjunct and the comparison with every probability on the original space are displayed; the summand order is the Lean expression Z i j * p j * p i.",
                DescribeRole.Definition, true),
            Entry("claim", "claim", "The negative-type extension question",
                Disp(IffFormula(V("claim"), ClaimBody())), QuestionQuotation()
                + " Only the second question is asserted: n is positive, metric ranges over all MetricSpace structures on Fin n, and letI selects that structure. The assertion includes existence of a first stop and requires every first-stop output to have positive mass and minimize energy. Finite labeling covers every nonempty finite metric space. The zero-size space is excluded because it has no probability measure.",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "Five points give a strict counterexample",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "Take the binary points (0,0,0,0,0), (1,1,0,0,1), (0,0,1,0,1), (0,1,0,1,1), (0,0,1,1,1). Scale Hamming distance by log(20/19). Multiplying their binary coordinates by √log(20/19) gives the required square-root isometric embedding. The similarity entries are (19/20) raised to their Hamming distances. "
                + "The first weighting has signs (+,+,−,−,+), so the second solve uses {0,1,4}. Both principal matrices are nonsingular. The second solve is nonnegative, with mass 12320200/11018319 and normalized vector (15961,22820,0,0,22820)/61601. Mixing this probability with weight 1/1000 of the point mass at index 3 yields a feasible probability of strictly smaller energy; the exact energy decrease is 1707687919/246404000000000. "
                + "This refutes the negative-type extension of Algorithm 1. The weighted-tree theorem remains within its stated hypotheses. The separate Euclidean-distance question, minimality of five points and correctness of a general re-entry algorithm remain unresolved here.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("bouafia-diversity-negative-type"),
                ResolutionKind.Refuted) : null);

    private static string QuestionQuotation() =>
        "Bouafia, arXiv:2605.03681v1, p. 18, §4.1, immediately after Theorem 4, verbatim: “Does DiversityMaximizingMeasure correctly compute the maximizing-diversity measure of all finite subsets of ℝⁿ? Of all finite metric spaces of negative type?”";
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula f, params Formula[] args) =>
        Seq(f, Parenthesized(Seq(Interleave(args))));
    private static Formula[] Interleave(Formula[] args) =>
        args.SelectMany((item, index) => index == 0 ? new[] { item } : new[] { Comma, Sp, item }).ToArray();
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula FinN => Call("Fin", V("n"));
    private static Formula MatrixN => Call("Matrix", FinN, FinN, Real);
    private static Formula Simplex => App(Qualified("Convexity", "StdSimplex"), Real, FinN);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(V("fun")), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula NotFormula(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula In(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Active(Formula k) => Call("active", V("Z"), k);
    private static Formula Weight(Formula a, Formula i) => Call("weighting", V("Z"), a, i);
    private static Formula MetricBind(Formula body) => All("n", Nat,
        Seq(OpenBracket, Call("MetricSpace", FinN), CloseBracket, Comma, Sp, body));
    private static Formula MatrixBind(Formula body) => All("n", Nat, All("Z", MatrixN, body));
    private static Formula Principal(Formula a) => App(Qualified("Matrix", "submatrix"), V("Z"),
        Lam("i", a, Call("val", V("i"))), Lam("j", a, Call("val", V("j"))));
    private static Formula WeightField(string mu, Formula i) =>
        App(Seq(V(mu), Dot, V("weights")), i);
    private static Formula Energy(Formula p) => Seq(Sum, Underscore, Grp(V("i"), Colon, FinN), Sp,
        Sum, Underscore, Grp(V("j"), Colon, FinN), Sp,
        Parenthesized(Seq(Parenthesized(Seq(Call("Z", V("i"), V("j")), Sp, Cdot, Sp, App(p, V("j")))),
            Sp, Cdot, Sp, App(p, V("i")))));

    private static Formula NegativeTypeFormula()
    {
        Formula distances = All("i", FinN, All("j", FinN,
            Equal(Call("dist", Call("f", V("i")), Call("f", V("j"))),
                App(Qualified("Real", "sqrt"), Call("dist", V("i"), V("j"))))));
        Formula body = Some("m", Nat, Some("f", Arrow(FinN,
            Call("EuclideanSpace", Real, Call("Fin", V("m")))),
            And(App(Qualified("Function", "Injective"), V("f")), distances)));
        return Disp(MetricBind(IffFormula(V("NegativeType"), body)));
    }
    private static Formula SimilarityFormula()
    {
        Formula kernel = App(Qualified("Real", "exp"),
            Seq(Minus, Parenthesized(Call("dist", V("i"), V("j")))));
        return Disp(MetricBind(All("i", FinN, All("j", FinN,
            Equal(Call("similarity", V("i"), V("j")), kernel)))));
    }
    private static Formula WeightingFormula()
    {
        Formula a = V("A");
        Formula one = Seq(Operatorname, Grp(V("fun")), Sp, Parenthesized(Seq(Dot, Colon, a)), Sp, Mapsto, Sp, D(1));
        Formula pair = Seq(Langle, Sp, V("i"), Comma, Sp, V("hi"), Sp, Rangle);
        Formula solve = App(Qualified("Matrix", "mulVec"), new Formula.Power(Parenthesized(Principal(a)), Seq(Minus, D(1))), one, pair);
        Formula conditional = Seq(V("if"), Sp, V("hi"), Colon, Sp, In(V("i"), a), Sp,
            V("then"), Sp, solve, Sp, V("else"), Sp, D(0));
        return Disp(MatrixBind(All("A", Call("Finset", FinN), All("i", FinN,
            Equal(Weight(a, V("i")), conditional)))));
    }
    private static Formula ActiveFormula() => Disp(MatrixBind(And(Equal(Active(D(0)), Qualified("Finset", "univ")),
        All("k", Nat, Equal(Active(Seq(V("k"), Plus, D(1))), App(Qualified("Finset", "filter"),
            Lam("i", FinN, Less(D(0), Weight(Active(V("k")), V("i")))), Active(V("k"))))))));
    private static Formula StoppedFormula() => Disp(MatrixBind(All("k", Nat, IffFormula(Call("stopped", V("Z"), V("k")),
        All("i", FinN, LessEq(D(0), Weight(Active(V("k")), V("i"))))))));
    private static Formula FirstStopFormula()
    {
        Formula visited = All("l", Nat, Imp(LessEq(V("l"), V("k")),
            And(App(Qualified("Finset", "Nonempty"), Active(V("l"))),
                Rel(App(Qualified("Matrix", "det"), Principal(Active(V("l")))), FormulaRelationOperator.NotEqual, D(0)))));
        Formula earlier = All("l", Nat, Imp(Less(V("l"), V("k")), NotFormula(Call("stopped", V("Z"), V("l")))));
        return Disp(MatrixBind(All("k", Nat, IffFormula(Call("FirstStop", V("Z"), V("k")),
            And(visited, And(earlier, Call("stopped", V("Z"), V("k"))))))));
    }
    private static Formula MassFormula() => Disp(MatrixBind(All("k", Nat, Equal(Call("mass", V("Z"), V("k")),
        Seq(Sum, Underscore, Grp(V("i"), Colon, FinN), Sp, Weight(Active(V("k")), V("i")))))));
    private static Formula OutputFormula() => Disp(MatrixBind(All("k", Nat, All("i", FinN,
        Equal(Call("output", V("Z"), V("k"), V("i")),
            new Formula.Fraction(Weight(Active(V("k")), V("i")), Call("mass", V("Z"), V("k"))))))));
    private static Formula MaximizingFormula()
    {
        Formula feasible = Some("mu", Simplex, All("i", FinN, Equal(WeightField("mu", V("i")), Call("p", V("i")))));
        Formula comparison = All("nu", Simplex, LessEq(Energy(V("p")), Energy(Seq(V("nu"), Dot, V("weights")))));
        return Disp(MatrixBind(All("p", Arrow(FinN, Real), IffFormula(Call("DiversityMaximizing", V("Z"), V("p")), And(feasible, comparison)))));
    }
    private static Formula ClaimBody()
    {
        Formula z = Seq(V("similarity"), Parenthesized(Seq(V("n"), Colon, Eq, V("n"))));
        Formula first = Call("FirstStop", z, V("k"));
        Formula good = And(Less(D(0), Call("mass", z, V("k"))),
            Call("DiversityMaximizing", z, Call("output", z, V("k"))));
        Formula assertion = Imp(Seq(V("NegativeType"), Parenthesized(Seq(V("n"), Colon, Eq, V("n")))),
            And(Some("k", Nat, first), All("k", Nat, Imp(first, good))));
        return All("n", Nat, Imp(Less(D(0), V("n")), All("metric", Call("MetricSpace", FinN),
            Seq(V("letI"), Sp, Colon, Eq, Sp, V("metric"), Semi, Sp, assertion))));
    }
}
