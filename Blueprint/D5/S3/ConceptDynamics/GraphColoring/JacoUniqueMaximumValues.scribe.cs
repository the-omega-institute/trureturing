using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoUniqueMaximumValuesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive maximum-degree values attained at exactly one recursive Jaco graph order are the complete source sequence, realized by one explicit infinite indexed family.",
        H("Unique values across all Jaco graph orders"),
        Blocks(
            Definition("unique", "UniqueValue", "Across-orders value uniqueness",
                "For an integer k, UniqueValue k means k is at least one and there is a natural order n at least two with the ordinary maximum degree of jaco n equal to k, such that every natural m at least two with that same maximum degree equals n. This is numerical value uniqueness across orders, not uniqueness of a maximizing vertex within one graph."),
            Definition("sequence", "sequenceValue", "The entire source sequence",
                "For every natural t, sequenceValue t is the integer floor of t times phi squared, minus one, where phi=(1+sqrt(5))/2 is Real.goldenRatio. The theorem uses every t at least one, exactly the displayed formula of arXiv:2507.16500v1, Conjecture 2.3, printed page 5. Zero is an auxiliary index outside the claimed sequence."),
            Definition("order", "realizingOrder", "One explicit order function",
                "Write B(q)=floor(q*phi) for integer q. The natural realizingOrder t is the nonnegative part of B(floor(t*phi squared))-1. The theorem proves it is at least two for every positive t, so this conversion truncates nothing on the source domain."),
            Describe.Lean(DescribeId.Create("jaco-unique-complete"), DeclarationHandle.Create(Prefix + "result"),
                H("Complete classification and infinite realizing family"),
                StatementSource.FromAuthor(Disp(And(
                    All("k", new Formula.Integers(), Imp(Le(D(1), K), Iff(Call("UniqueValue", K),
                        Ex("t", Nat(), And(Le(D(1), T), Equal(K, A(T))))))),
                    Ex("r", Seq(Nat(), Sp, To, Sp, Nat()), And(Equal(R, new Formula.NamedConstant(FormulaIdentifier.Create("realizingOrder"))),
                        All("t", Nat(), Imp(Le(D(1), T), And(Le(D(2), Rt), And(Le(D(1), A(T)),
                            And(Equal(Delta(Rt), A(T)), All("m", Nat(), Imp(Le(D(1), M),
                                Imp(Equal(Delta(M), A(T)), Equal(M, Rt)))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Certificates/kok2025jaco")),
                Blocks(Paragraph(Text(
                    "Maximum degrees are viewed as integers through the natural embedding. The graph is the existing underlying simple graph of the original f(x)=x recursive Jaco construction, not a graph defined by the desired degree formula. Reuse JacoMaximumDegree.result for its maximum degree at all n at least two. Irrational floor inversion gives the entire fiber B(k+1)-1 <= n <= B(k+2)-2. Both endpoints belong to the positive-order source domain. The fiber is a singleton exactly when floor((k+2)/phi)=floor((k+1)/phi). A strict jump is equivalent to k+1 belonging to the positive lower Beatty sequence. Direct application of Mathlib's Irrational.beattySeq_symmDiff_beattySeq_pos at phi and phi squared gives precisely its complementary upper Beatty sequence. This proves both directions for every positive integer k.")),
                    Paragraph(Text(
                    "For each positive t, the same explicit function realizingOrder selects the lower endpoint of that singleton fiber. Its degree is sequenceValue t, which is positive. The singleton graph has maximum degree zero, so uniqueness extends to every positive m including one. Thus G_t=jaco(realizingOrder t) is one whole infinite indexed realizing family. The source's family notation is read memberwise, its existence allows selection of corresponding orders, and the parameter is ordinary degree restricted to globally unique positive values. No total parameter on ineligible graphs or requirement G_t=J_t is added. These are the explicit source conventions; they do not assert an author-issued correction. Conjecture 2.5 concerns a different vertex-count property. The separately reported MathDB answers concern 2.2 and 2.5; neither report is attributed here to 2.3. Literature screening and external priority remain bounded; no worldwide novelty claim is made."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kok-jaco-unique-maximum-values"),
                    ResolutionKind.Proved)))));

    private static Formula K => F.Id("k");
    private static Formula T => F.Id("t");
    private static Formula M => F.Id("m");
    private static Formula R => F.Id("r");
    private static Formula Rt => Call("r", T);
    private static Formula A(Formula t) => Call("sequenceValue", t);
    private static Formula Delta(Formula n) => Call("maxDegree", Call("jaco", n));
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Ex(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
    private static DocumentBlock Definition(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("jaco-unique-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
