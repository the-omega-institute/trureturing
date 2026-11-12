using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickConvexDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickConvex.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/gheondeagudderjonas2005infimum");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "General convex maximal hockey equality for actual finite reverse tests and arbitrary singular matrix pairs.",
        H("General convex equality on the common interior"),
        Blocks(
            Paragraph(Text("The finite source class is exactly the existing ReverseTest A B k, with k ranging over all natural numbers. Its p and q are nonnegative real functions on Fin k, and its density-matrix preparation realizes the original A and B. No trace normalization, invertibility, nonzero-pair or nonempty-dimension hypothesis is imposed. MaximalHockeyStickAllL1Convex identifies this finite infimum with the actual all-s-finite-L1 infimum using MaximalHockeyStickL1ReverseTest.source_class_infimum_eq, and transfers the classification with finiteness stated for that actual source class. No arbitrary von Neumann algebra theorem is asserted.")),
            Node("affineMass", "The original finite affine mass",
                "For the real convex generator f, affineMass f A B is f(1) Tr(B) + f'_+(1)(Tr(A)-Tr(B)). The derivative is the actual right derivative from CurvatureHingeRepresentation. Both traces retain their original arbitrary values.", false),
            Node("hinge", "The two scalar orientations",
                "For t in the strictly positive subtype, hinge u v t is max(t v-u,0) when t <= 1 and max(u-t v,0) when t > 1. Thus the full atom at one belongs to the negative branch.", false),
            Node("testKernel", "The actual finite classical hockey kernel",
                "testKernel R t is the sum over Fin k of hinge (R.p i) (R.q i) t. It is nonnegative and measurable, and differs from maximalKernel by the actual positive-orientation gap at every positive threshold.", false),
            Node("maximalKernel", "The actual optimized overlap kernel",
                "Write O(t) for the supremum of Re Tr(X) over the actual positive overlaps 0 <= X <= A and X <= t B. For t <= 1 the kernel is t Tr(B)-O(t); for t > 1 it is Tr(A)-O(t). Both branches are nonnegative. The optimization is over the actual singular matrix pair.", false),
            Node("finiteCost", "The full closed-perspective finite cost",
                "finiteCost hf R is the EReal sum over Fin k of closedPerspective hf (R.p i) (R.q i). In the positive quadrant the summand is q f(p/q); on each nonzero axis it is the positive mass times the proved convex endpoint limit; at the origin it is zero even with infinite endpoints. The scalar supplier constructs the actual locally finite curvature from the right derivative for every real f convex on Ioi 0. Its exact representation proves that finiteCost is affineMass plus the nonnegative curvature integral of testKernel, including infinite values.", false),
            Node("maximalValue", "Infimum over every actual finite test",
                "maximalValue hf A B is the EReal infimum of finiteCost over every k and every ReverseTest A B k. Its definition assumes neither a minimizing test nor a bound on alphabet size. A real finite infimum yields a sequence of actual tests with cost strictly below c+1/(j+1); every such cost is finite.", false),
            Node("hockeyValue", "The actual integrated maximal hockey value",
                "hockeyValue hf A B is affineMass plus the ENNReal curvature integral of maximalKernel, embedded in EReal. Equivalently its two nonnegative integrals are over (0,1] and (1,infinity). This is the finite-affine-support convention, so infinite endpoints or infinite total curvature do not introduce an infinite difference.", false),
            Node("commute_implies_integrated_eq", "Sufficiency for every convex generator and extended value",
                "For every finite PSD pair, let S=A+B, C=normalize(S,A), and P=interiorProjection(C). If PSP commutes with PCP, then maximalValue hf A B equals hockeyValue hf A B for every real f convex on the positive ray. No full-support or finite-value hypothesis is needed in this direction. The actual canonical spectral test supplied by quadratic_reverse_test_attained_profile has exactly maximalKernel at every positive threshold. Its actual closed-perspective cost integrates that profile, and the defining infimum is sandwiched between this cost and the hockey lower bound. This proves the converse with infinite endpoint values, rather than assuming canonical optimality for general f.", true),
            Node("integrated_eq_iff_commute", "The finite-value full-support classification",
                "For every finite type n, every pair A,B of PSD complex n by n matrices, every real f convex on Ioi 0 whose constructed curvature is positive on every nonempty open set, and every real c satisfying maximalValue hf A B = c, equality maximalValue hf A B = hockeyValue hf A B is equivalent to (PSP)(PCP)=(PCP)(PSP), with S=A+B, C=normalize(S,A), P=interiorProjection(C). Local finiteness is supplied by the constructed curvature. The statement includes zero and singular pairs and the empty matrix type. Finite-cost approximate tests have integrable nonnegative gaps; their costs split as hockeyValue plus the real gap integral. Equality and the 1/(j+1) bounds force those integrals to zero, and vanishing_curvature_gaps_imply_commute supplies the original-pair commutator. No general-f attainment theorem is used. Operator-convex generators satisfying the same curvature and finite-value hypotheses are included by this scalar-convex theorem. Necessity from equality of two infinite values is not asserted.", true),
            Paragraph(Text("Attribution: the source equality question is Hiai, Mosonyi and Tomamichel, Hockey stick f-divergences, arXiv:2607.08760v1, final equality question. Hiai's canonical spectral reverse-test construction and operator-convex optimality are antecedents, rather than new claims. The GGJ2005 result documented by the Library attribution is a localization antecedent for separating common-support overlap geometry from endpoint pieces. The finite proof consumes the repository's actual finite spectral and quadratic results and its scalar Stieltjes construction. Its all-L1 application also consumes the exact one-cost finite-moment source bridge following Bayer-Teichmann's proof of Tchakaloff's theorem. No general-convex attainment result is assumed. The full-support approximate-test integration is a repository derivation; worldwide priority is unresolved."))
        )));

    private static DocumentBlock Node(string name, string heading, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-convex-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
