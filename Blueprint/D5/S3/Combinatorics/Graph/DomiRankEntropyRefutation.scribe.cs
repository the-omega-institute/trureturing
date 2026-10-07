using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DomiRankEntropyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/zhangzhao2026domirank");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "DomiRank entropy can increase with competition on a connected nonregular simple graph. A six-vertex graph gives an exact entropy gap and a whole increasing interval; independent clones give the same behavior on 6m vertices for every positive integer m.",
        H("Increasing DomiRank entropy on connected nonregular graphs"),
        Blocks(
            Node("nonregular", "Unequal degrees", NonregularFormula(),
                "Nonregular means that two vertices have different degrees. The finite sum counts the neighbors of each vertex.",
                "Nonregular", AssessedProvenance.FromLiterature(Source)),
            Node("clipped", "Positive scores", ClippedFormula(),
                "Negative scores are replaced by zero. This is the positive-part convention used for the entropy distribution.",
                "clipped", AssessedProvenance.FromLiterature(Source)),
            Node("normalized", "Normalizing the positive part", NormalizedFormula(),
                "The positive scores are divided by their total mass. Real division gives a total definition, including when the denominator is zero. For connected nonregular graphs at stable positive parameters the proof establishes invertibility of I+sA, the equilibrium equation and strictly positive clipped mass; the claim requires no additional normalizer premise.",
                "normalized", AssessedProvenance.FromLiterature(Source)),
            Node("entropy", "Shannon entropy in bits", EntropyFormula(),
                "The finite Shannon entropy is the negative sum of p_i log(p_i), with the natural logarithm and the usual zero contribution at p_i=0. Division by log(2) converts it to bits. shannonEntropy is the existing finite entropy definition.",
                "entropyBits", AssessedProvenance.FromLiterature(Source)),
            Node("minimum", "The least adjacency eigenvalue", MinimumFormula(),
                "The real adjacency matrix is Hermitian. On a nonempty finite vertex type, spectralMinimum is the minimum of its real eigenvalues; infPrime denotes Finset.inf' over all indices. The empty type is assigned zero. The claim has n>0, and its stable domain is 0<s<-1/spectralMinimum(G).",
                "spectralMinimum", AssessedProvenance.FromLiterature(Source)),
            Node("adjacency", "The actual adjacency matrix", GraphBinders(Equal(Call("graphAdj", Id("G")), Call("adjMatrix", Id("G"), Reals())), false),
                "graphAdj is Mathlib's real adjacency matrix of the given simple graph, with entries one on edges and zero elsewhere.",
                "graphAdj", AssessedProvenance.FromLiterature(Source)),
            Node("degrees", "The degree vector", GraphBinders(Equal(Call("graphDegrees", Id("G")), MulVector(Call("graphAdj", Id("G")), Ones())), false),
                "Multiplying adjacency by the all-ones vector gives the actual degree vector.",
                "graphDegrees", AssessedProvenance.FromLiterature(Source)),
            Node("gamma", "The inverse equilibrium", GammaFormula(),
                "The source equilibrium uses theta=1 and sigma=s. The inverse is Mathlib's nonsingular matrix inverse. On the stable spectral domain I+sA is invertible, so this definition satisfies the actual equilibrium equation. No scalar proxy replaces the adjacency or inverse.",
                "graphGamma", AssessedProvenance.FromLiterature(Source)),
            Node("graph-entropy", "Entropy of the equilibrium", GraphBinders(All("s", Reals(), Equal(Call("graphEntropyBits", Id("G"), Id("s")), Call("entropyBits", Call("normalized", Call("graphGamma", Id("G"), Id("s")))))), true),
                "The inverse equilibrium is positively clipped and normalized before taking Shannon entropy in bits.",
                "graphEntropyBits", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The unconditional question in Remark 4.6", ClaimFormula(),
                "Remark 4.6 asks whether the DomiRank entropy of a connected non-regular graph decreases monotonically with sigma. claim expresses nonincrease for every finite connected nonregular simple graph and every ordered pair of positive parameters in the full stable spectral domain. Fin(n) labels the vertices without restricting finite graph isomorphism classes. The conditional Theorem 4.5 and the star-minimum Conjecture 4.7 are separate statements.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("domirank-result"), DeclarationHandle.Create(Prefix + "result"),
                H("An exact pair, a whole interval, and independent clones"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take vertices 0 through 5 and edges {0,4}, {0,5}, {1,2}, {1,3}, {1,4}, {2,3}, {2,4}. This graph is connected, has degree vector (2,3,3,2,3,1), and has least eigenvalue in [-3,-1]. Its actual equilibrium vectors at 1/20 and 1/6 are (397,577,577,378,576,198)/4357 and (33,45,45,28,44,16)/129. Their coordinates are strictly between zero and one. Rational logarithm bounds with integral remainders give H(1/6)-H(1/20)>1/(500 log(2)).")),
                    Paragraph(Text("For every finite nonempty graph with positive degrees d, put D=sum_i d_i, w_i=d_i/D and q_i=(Ad)_i/d_i. The derivative at zero of the normalized inverse extension is (sum_i w_i q_i log(d_i) - (sum_i w_i q_i)(sum_i w_i log(d_i)))/log(2). For this graph it equals log(27/2)/(49 log(2))>0. Explicit derivative bounds give H(a)<H(b) for every 0<a<b<delta, delta=1/5000000, with admissible parameters and scores strictly between zero and one. Zero is only a point of the normalized inverse extension; clipped Gamma at zero does not give that extension and zero is never a source-domain point.")),
                    Paragraph(Text("For every natural m>0, replace each vertex by m independent clones and every edge by all edges between its clone classes. On Fin(6) x Fin(m) the actual adjacency depends only on the first coordinates. The graph is connected and nonregular, has 6m vertices and least eigenvalue in [-3m,-m]. For 0<s<1/(3m), the inverse equilibrium replicates Gamma_G(ms), the probabilities satisfy P_m(s)_(i,j)=P_G(ms)_i/m, and H_m(s)=H_G(ms)+log(m)/log(2). Thus the pair 1/(20m),1/(6m) has the same strict entropy gap, and every 0<a<b<delta/m has admissible parameters, positive scores below one, and H_m(a)<H_m(b).")),
                    Paragraph(Text("These covariance, interval and clone identities are local to result. The family at m=1 transfers both the exact-pair increment and an interval increment back to the base graph. Their sum is strictly positive, whereas claim would make both increments nonpositive. This proves the negation of the universal source assertion. The reduced cubic coordinate denominator is not asserted to be the adjacency determinant."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-zhao-2026-domirank-entropy-monotonicity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("domirank-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(Id("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula SumOver(string i, Formula x) => Seq(F.Sum, Underscore, Grp(Id(i)), Sp, x);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Ones() => Seq(Par(Seq(Id("i"), Sp, Mapsto, Sp, D(1))));
    private static Formula MulVector(Formula a, Formula b) => Call("mulVec", a, b);
    private static Formula Finite(Formula body, bool equality) => All("W", Id("Type"),
        Instance(Call("Fintype", Id("W")), equality ? Instance(Call("DecidableEq", Id("W")), body) : body));
    private static Formula GraphBinders(Formula body, bool equality) => Finite(
        All("G", Call("SimpleGraph", Id("W")), Instance(Call("DecidableRel", Call("Adj", Id("G"))), body)), equality);

    private static Formula NonregularFormula()
    {
        Formula Count(string vertex) => SumOver("w", Call("ite", Call("Adj", Id("G"), Id(vertex), Id("w")), D(1), D(0)));
        Formula exists = Seq(Exists, Sp, Par(Seq(Id("u"), Sp, Colon, Sp, Id("W"))), Sp,
            Par(Seq(Id("v"), Sp, Colon, Sp, Id("W"))), Comma, Sp,
            new Formula.Relation(Count("u"), FormulaRelationOperator.NotEqual, Count("v")));
        return GraphBinders(Logic(Call("Nonregular", Id("G")), FormulaLogicOperator.Iff, exists), true);
    }

    private static Formula ClippedFormula()
    {
        Formula value = Equal(Call("clipped", Id("p"), Id("i")),
            Call("max", Call("p", Id("i")), D(0)));
        return All("W", Id("Type"), All("p", Arrow(Id("W"), Reals()), All("i", Id("W"), value)));
    }

    private static Formula NormalizedFormula()
    {
        Formula ratio = new Formula.Fraction(Call("clipped", Id("p"), Id("i")),
            SumOver("j", Call("clipped", Id("p"), Id("j"))));
        Formula value = Equal(Call("normalized", Id("p"), Id("i")), ratio);
        return Finite(All("p", Arrow(Id("W"), Reals()), All("i", Id("W"), value)), false);
    }

    private static Formula EntropyFormula() => Finite(All("p", Arrow(Id("W"), Reals()),
        Equal(Call("entropyBits", Id("p")), new Formula.Fraction(Call("shannonEntropy", Id("p")), Call("log", D(2))))), false);

    private static Formula MinimumFormula()
    {
        Formula values = Call("eigenvalues", Call("isHermitianAdjMatrix", Id("G"), Reals()));
        Formula cases = Seq(Left, OpenBrace, new Formula.Aligned([
            Seq(Call("infPrime", Call("univ", Id("W")), values), Sp, Amp, Sp, F.Text, Grp(Id("if")), Sp, Call("Nonempty", Id("W"))),
            Seq(D(0), Sp, Amp, Sp, F.Text, Grp(Id("otherwise")))]), Right, Dot);
        return GraphBinders(Equal(Call("spectralMinimum", Id("G")), cases), false);
    }

    private static Formula GammaFormula()
    {
        Formula s = Id("s"), a = Call("graphAdj", Id("G"));
        Formula matrix = new Formula.Binary(D(1), FormulaBinaryOperator.Add, new Formula.Binary(s, FormulaBinaryOperator.Multiply, a));
        Formula inverse = new Formula.Power(Par(matrix), Seq(Minus, D(1)));
        return GraphBinders(All("s", Reals(), Equal(Call("graphGamma", Id("G"), s),
            new Formula.Binary(s, FormulaBinaryOperator.Multiply, MulVector(inverse, Call("graphDegrees", Id("G")))))), true);
    }

    private static Formula ClaimFormula()
    {
        Formula Stable(string s) => Logic(Lt(D(0), Id(s)), FormulaLogicOperator.And,
            Lt(Id(s), new Formula.Fraction(Seq(Minus, D(1)), Call("spectralMinimum", Id("G")))));
        Formula conclusion = new Formula.Relation(Call("graphEntropyBits", Id("G"), Id("tau")),
            FormulaRelationOperator.LessThanOrEqual, Call("graphEntropyBits", Id("G"), Id("sigma")));
        Formula parameters = All("sigma", Reals(), All("tau", Reals(),
            Implies(Stable("sigma"), Implies(Stable("tau"), Implies(Lt(Id("sigma"), Id("tau")), conclusion)))));
        Formula graphs = All("G", Call("SimpleGraph", Call("Fin", Id("n"))),
            Instance(Call("DecidableRel", Call("Adj", Id("G"))),
                Implies(Call("Connected", Id("G")), Implies(Call("Nonregular", Id("G")), parameters))));
        return Logic(Id("claim"), FormulaLogicOperator.Iff,
            All("n", Naturals(), Implies(Lt(D(0), Id("n")), graphs)));
    }
}
