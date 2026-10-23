using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class HanceTwentyFourCellThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumContext/HanceTwentyFourCellThreshold.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/hance2026fourquestions");
    private static readonly LibraryNoteRef Rac = LibraryNoteRef.Create("D5/L/QuantumContext/chailloux2016parityoblivious");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The twenty-four-cell preparation subtheory admits a preparation-noncontextual model exactly up to visibility one half.",
        H("Exact preparation-noncontextuality threshold of the twenty-four-cell"),
        Blocks(
            Def("Signs", "Four signs", "Signs is Bool times Bool times Bool times Bool. True denotes plus one and false denotes minus one."),
            Def("Vertex", "All twenty-four preparation labels", "Vertex is the disjoint union of Fin 4 times Bool and Signs. Its first eight labels are the signed coordinate axes; its remaining sixteen labels are all half-sign vectors. No parity class is omitted."),
            Def("Question", "The twelve sharp binary questions", "Question is Fin 4 disjoint union Bool times Bool times Bool. The four coordinate directions and eight half-sign directions with positive first coordinate represent all twelve antipodal pairs. Both binary outcomes are retained."),
            Def("sign", "Signs as real numbers", "For every Boolean b, sign b is one if b is true and minus one otherwise."),
            Def("bits", "The four coordinates of a sign tuple", "For every sign tuple s, bits s is the Fin 4 indexed vector of its four entries in tuple order."),
            Def("vertex", "Preparation vectors", "For every coordinate i and Boolean b, vertex (inl (i,b)) has sign b in coordinate i and zero elsewhere. For every sign tuple s, vertex (inr s) has coordinate sign (bits s j) divided by two at every j. Thus its image is exactly the union of all signed coordinate axes and all sixteen half-sign vectors."),
            Def("question", "Sharp measurement directions", "For every coordinate i, question (inl i) is the positive coordinate axis. For every triple (a,b,c), question (inr (a,b,c)) is the vector (1,sign a,sign b,sign c) divided by two."),
            Def("dot", "Real coordinate pairing", "For every pair of real Fin 4 vectors x and y, dot x y is the sum over all four coordinates of x i times y i."),
            Def("statistics", "Statistics of every classical preparation mixture", "For every real visibility lambda, every nonnegative weight vector alpha on Vertex, every question n and Boolean outcome b, statistics lambda alpha n b is the sum over x of alpha x times (1 + sign b times lambda times dot (question n) (vertex x)) divided by two. Probability mixtures have total weight one. Noise acts on preparations only; there is exactly one visibility factor. Classical mixtures of questions take the corresponding convex sums of these statistics."),
            Def("mixture", "Countably additive ontic preparation mixtures", "For every measurable space Omega, every nonnegative weight vector alpha and every family mu of measures on Omega, mixture alpha mu is the finite sum of alpha x times mu x as measures. Real nonnegative weights are coerced through NNReal to ENNReal. This is convex randomization when the weights sum to one."),
            Def("Model", "An original measurable ontological model", "For every real lambda and every arbitrary measurable space Omega, Model lambda Omega consists of: one countably additive probability measure preparation x for each of all twenty-four labels; a real measurable response n b on Omega for every sharp question and binary outcome; nonnegativity at every ontic state; response n true plus response n false equal to one; and the exact integral of response n b against preparation x equal to (1 + sign b times lambda times dot (question n) (vertex x)) divided by two. Responses may be stochastic. For every pair alpha,beta of nonnegative preparation weight vectors of total weight one, equality of statistics for every question and both outcomes implies equality of the entire ontic mixture measures. This quantifies over every operationally equal pair, not just the equivalences used in the upper argument. Convex randomization extends preparation measures and measurement responses by their actual finite sums. No measurement-noncontextuality, outcome determinism, density representation, topology or countable-generation premise is imposed."),
            Def("admissible", "Existence on an arbitrary measurable ontic space", "For every universe level u and every real lambda, admissible at level u means that there exist a type Omega in Type u, a measurable-space structure on Omega, and an inhabitant of Model lambda Omega. The result is polymorphic in u. The upper argument applies to every such space; the lower argument lifts its finite construction into the chosen universe."),
            Def("anti", "Opposite sign tuple", "For every sign tuple s, anti s negates each of its four Boolean entries."),
            Def("zeroWeights", "The coordinate midpoint mixture", "zeroWeights assigns one half to each of the two preparations on coordinate zero, and zero to all other preparations. Its operational vector is zero at every visibility."),
            Def("boundWeights", "A zero-vector mixture for every sign tuple", "For every s, boundWeights s assigns one sixth to each of the four signed axis preparations selected by s, and one third to the half-sign preparation with sign tuple anti s. All other weights are zero. The weights sum to one and their vector is zero, so this mixture is operationally equal to zeroWeights."),
            Def("Ontic", "The twenty-four explicit ontic states", "Ontic is Fin 6 times Bool times Bool. The six labels select an unordered pair of different coordinates, and the two Boolean entries select their signs."),
            Def("pairs", "The six coordinate pairs", "In Fin 6 order, pairs is (0,1), (0,2), (0,3), (1,2), (1,3), (2,3). Each coordinate pair occurs exactly once."),
            Def("ontic", "Ontic root vectors", "For every ontic label u, ontic u is sign u's first Boolean times the first selected coordinate axis plus sign u's second Boolean times the second selected coordinate axis. These are all vectors epsilon e_i + delta e_j with i less than j."),
            Def("weight", "The full preparation model", "For every real lambda, preparation x and ontic label u, weight lambda x u is (1 + 2 times lambda times dot (ontic u) (vertex x)) divided by twenty-four. When zero is at most lambda and lambda is at most one half, these are nonnegative and sum to one. At lambda zero every preparation has the same uniform distribution."),
            Describe.Lean(
                DescribeId.Create("hance-response"), DeclarationHandle.Create(Prefix + "onticResponse"),
                H("Stochastic binary responses"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every question n, Boolean b and ontic label u, onticResponse n b u is (1 + sign b times dot (ontic u) (question n)) divided by two. Both responses are nonnegative and sum to one. Their definition has no visibility factor."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hance-exact-threshold"), DeclarationHandle.Create(Prefix + "result"),
                H("Exact threshold for the full preparation scenario"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source, Rac),
                Blocks(
                    Paragraph(Text("For every universe level u and every real visibility lambda in the closed interval from zero to one, the original measurable-space model exists if and only if lambda is at most one half. The ontic existence quantifier includes arbitrary measurable spaces and countably additive probability preparations; the statement includes all twenty-four preparations, all twelve sharp binary questions, all classical mixtures and every operational preparation equivalence. The zero-visibility collapse is included.")),
                    Paragraph(Text("For the upper implication, multiply the four stochastic coordinate responses to form a nonnegative measurable weight for each of the sixteen sign tuples. Their sum is one and their coordinate marginals are the original responses. Integrate the zero-vector mixture identities against these weights. The omitted half-sign term has nonnegative integral, and summing the remaining inequalities gives 4(1+lambda) at most 6. This is the known parity-oblivious random-access-code obstruction, applied directly to the original measures without a finite-space reduction.")),
                    Paragraph(Text("For the converse, place the displayed weights and responses on all twenty-four ontic root vectors. Exact sign symmetry gives total preparation mass one and the required statistics. Coordinate questions determine the actual noisy mixture coordinates. For any normalized alpha the ontic mass at u is (1 + 2 times dot (ontic u) with lambda times the alpha-weighted preparation vector) divided by twenty-four. Therefore every operationally equal pair has identical ontic measures, including at lambda zero. The exact full-scenario attainment supplies the threshold; no separate novelty claim is made for the upper bound or the generic measure and convexity facts."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hance-2026-twenty-four-cell-preparation-threshold"), ResolutionKind.Proved)))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("hance-" + name.ToLowerInvariant()
            + (name is "Signs" or "Vertex" or "Question" or "Model" or "Ontic" ? "-type" : "")),
        DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(name), Colon, type, Close, Comma, Sp, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula ResultFormula()
    {
        Formula u = F.Id("u"), lambda = F.Id("lambda");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula range = Seq(Open, D(0), Leq, Sp, lambda, Land, Sp, lambda, Leq, Sp, D(1), Close);
        Formula iff = Seq(Open, Call("admissible", u, lambda), Iff, Sp, lambda, Leq, Sp,
            new Formula.Fraction(D(1), D(2)), Close);
        return Disp(All("u", Call("Level"), All("lambda", real, Seq(range, Implies, Sp, iff))));
    }
}
