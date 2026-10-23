using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class DeterministicSimplicialDegreeShiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/StatisticalMechanics/dorogovtsevkrapivsky2025deterministic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The distinct upper degrees in positive dimension are zero together with the vertex degrees at the dimension-shifted generation.",
        H("The dimension shift for deterministic simplicial degree sets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dsc"), DeclarationHandle.Create(Prefix + "dsc"),
                H("The growing family of nonempty faces"),
                StatementSource.FromAuthor(Disp(DscFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The initial family consists of the singleton containing v₀. At step s + 1, "
                    + "each existing face σ contributes a vertex v(s + 1, σ) and every face obtained "
                    + "by adjoining that vertex to a subset β of σ, including the empty subset. "
                    + "All earlier faces remain. These are finite sets of nonempty faces; the empty "
                    + "face is omitted from the family. The single-vertex initial condition and growth "
                    + "rule are described in Section II.1 and the abstract (TeX lines 118 and 82). "
                    + "The recursion itself accepts any labels; injectivity and avoidance of v₀ "
                    + "are assumptions of the degree-set identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("upper-degree"), DeclarationHandle.Create(Prefix + "upperDegree"),
                H("The upper degree of a face"),
                StatementSource.FromAuthor(Disp(UpperDegreeFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite family C and a finite set τ of vertices, the upper degree counts "
                    + "the members ρ of C that contain τ and have exactly one more vertex. "
                    + "This agrees with the upper degree of a simplex described at TeX line 106. "
                    + "The expression is defined for arbitrary C and τ, without requiring τ to belong "
                    + "to C. Every cardinality and degree in the formula is a natural number."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("degree-set"), DeclarationHandle.Create(Prefix + "degreeSet"),
                H("The set of distinct degrees in a dimension"),
                StatementSource.FromAuthor(Disp(DegreeSetFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A natural number k belongs to this set precisely when a face τ in C has "
                    + "d + 1 vertices and upper degree k. Multiplicities are discarded. Thus this "
                    + "set expresses the same distinct values as the increasing lists K⁽ᵈ⁾(n) "
                    + "in Section II.3 (TeX lines 427–503). An empty collection of faces of the "
                    + "specified size gives the empty degree set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The degree-set identity"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Named("claim"), Name("Prop")),
                    Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The labeling is injective as a function of the pair consisting of the step "
                    + "and the parent face, and no label equals v₀. For every natural dimension "
                    + "d at least one and generation n at least d + 1, the d-degree set is the "
                    + "vertex-degree set at generation n − d with zero adjoined. The subtraction "
                    + "is natural subtraction; the stated inequalities imply n − d ≥ 1. "
                    + "This is relation (34), stated as a conjecture at TeX lines 505–510, "
                    + "with the labeling assumptions and the sets of distinct values made explicit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The identity holds in every positive dimension"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix V, v₀ and v satisfying the two labeling hypotheses. For a face τ "
                        + "in a family C, write L_C(τ) for the finite family of sets α "
                        + "disjoint from τ such that τ ∪ α belongs to C. Equivalently, take all "
                        + "members of C containing τ and remove τ from each. Define the binomial "
                        + "transform B_f(r) = ∑_{j=0}^r binom(r,j) f(j). Start with w₀(r) equal "
                        + "to one when r = 1 and zero otherwise, and set "
                        + "w_{q+1}(r) = w_q(r) + ∑_{j=0}^r binom(r,j) w_q(j + 1). "
                        + "Let A(t,r) = B_{w_t}(r). These natural numbers describe the evolution "
                        + "of the number of vertices among the residual faces.")),
                    Paragraph(Text(
                        "A face at generation n + 1 is either an earlier face or has the form "
                        + "{v(n + 1, σ)} ∪ β for an earlier parent σ and a subset β of σ. "
                        + "Induction shows that every vertex in a generation-n face is either v₀ "
                        + "or a label from a step at most n. Injectivity and avoidance of v₀ "
                        + "therefore make all later labels absent from earlier faces. Every face "
                        + "at generation n has between one and n + 1 vertices. The family is "
                        + "closed under nonempty subsets: a subset of a new face either contains "
                        + "its new vertex and is produced by the same parent, or is an earlier "
                        + "subset of that parent. Repeatedly adjoining the vertex assigned to a "
                        + "largest face produces a face with n + 1 vertices. Taking subsets yields "
                        + "a face of every cardinality from one through n + 1.")),
                    Paragraph(Text(
                        "The description of L_C(τ) by disjoint sets follows because removing τ "
                        + "and adjoining it again are inverse on the faces containing τ. Also, "
                        + "a label v(n + 1, σ) belongs to a new face {v(n + 1, ρ)} ∪ β "
                        + "exactly when σ = ρ: it cannot belong to the earlier subset β, and "
                        + "equality of the two new labels determines the parent. The upper degree "
                        + "of τ is ∑_{α ∈ L_C(τ)} w₀(|α|), since these are precisely the "
                        + "singleton residual sets.")),
                    Paragraph(Text(
                        "Fix a face τ at generation n, let C be the family at that generation, "
                        + "and put L = L_C(τ). Its residual family after "
                        + "one step consists of L together with all {u_α} ∪ β, where α belongs "
                        + "to L, β is a subset of α, and u_α = v(n + 1, τ ∪ α). Indeed, "
                        + "a new face containing τ must come from a parent containing τ; removing "
                        + "τ identifies that parent with τ ∪ α. Conversely every such choice "
                        + "produces a face containing τ. The vertices u_α are distinct and occur "
                        + "in no earlier residual set. Hence the new families for different α "
                        + "are pairwise disjoint and are disjoint from L. For any function f on "
                        + "natural numbers, the sum of f of cardinalities after this step is "
                        + "∑_{α ∈ L}(f(|α|) + ∑_{j=0}^{|α|} binom(|α|,j) f(j + 1)). "
                        + "Here adjoining u_α increases cardinality by one, and subsets of each "
                        + "cardinality j are counted by the binomial coefficient.")),
                    Paragraph(Text(
                        "Applying this equality with f = w_q turns a sum of w_q at the next "
                        + "generation into a sum of w_{q+1} at the present generation. Earlier "
                        + "faces persist, so induction over t gives a sum of w_{q+t} at birth "
                        + "after t further steps. For a face {v(s + 1, σ)} ∪ η born from "
                        + "η ⊆ σ, the residual family at birth is exactly the powerset of "
                        + "σ ∖ η. Its new vertex forces the parent of every containing new "
                        + "face to be σ, while disjointness removes η. Grouping the residual "
                        + "subsets by cardinality consequently gives upper degree "
                        + "A(t, |σ| − |η|) at generation s + 1 + t. Every face is either "
                        + "the primordial singleton or has this birth description, by induction "
                        + "on the generation. The primordial singleton has residual family "
                        + "{∅} initially, so its degree at generation n is A(n,0).")),
                    Paragraph(Text(
                        "For d ≥ 1, a face with d + 1 vertices cannot be the primordial "
                        + "singleton. In its birth description |η| = d. Set r = |σ| − |η| "
                        + "and let t be its age. Since |σ| ≤ s + 1 and s + 1 + t = n, "
                        + "one has t + r ≤ n − d. Conversely, for any natural t,r with "
                        + "this inequality, set s = n − t − 1, choose at generation s a "
                        + "parent σ of cardinality d + r, and choose η ⊆ σ of cardinality d. "
                        + "The face {v(s + 1, σ)} ∪ η persists to generation n and has "
                        + "degree A(t,r). Thus the d-degree set consists exactly of these "
                        + "values A(t,r).")),
                    Paragraph(Text(
                        "At generation m the vertex degrees consist of A(m,0) from the "
                        + "primordial vertex and the values A(t,r) with 1 ≤ r and t + r ≤ m. "
                        + "For a new vertex η is empty, so r is the nonzero cardinality of "
                        + "its parent. Conversely, each such pair is realized by choosing a "
                        + "parent of cardinality r at generation m − t − 1 and adjoining "
                        + "its assigned vertex.")),
                    Paragraph(Text(
                        "The binomial recurrence gives A(0,0) = 0 and A(t + 1,0) = A(t,1). "
                        + "For m ≥ 1, compare all pairs t,r with t + r ≤ m to the vertex "
                        + "description. A pair with r ≥ 1 already occurs there. If r = 0 "
                        + "and t ≥ 1, replace (t,0) by (t − 1,1), preserving its value "
                        + "and the bound on the sum. The sole remaining case (0,0) gives zero. "
                        + "In the reverse direction zero comes from (0,0), the primordial "
                        + "value comes from (m,0), and all other vertex values already satisfy "
                        + "the bound. Taking m = n − d ≥ 1 proves the asserted equality."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dorogovtsev-krapivsky-2025-deterministic-simplicial-degree-shift"),
                    ResolutionKind.Proved)))));

    private static Formula DscFormula()
    {
        var initial = Equal(Typed(Dsc(D(0)), FinsetOf(FinsetOf(X("V")))),
            Singleton(Singleton(VZero)));
        var additions = At(Name("Finset", "biUnion"), Dsc(X("s")),
            LambdaOf(SigmaLower, FinsetOf(X("V")),
                At(Name("Finset", "image"),
                    LambdaOf(Beta, FinsetOf(X("V")),
                        At(Name("insert"), At(X("v"), Add(X("s"), D(1)), SigmaLower), Beta)),
                    At(Name("Finset", "powerset"), SigmaLower))));
        var step = All(X("s"), Naturals, Equal(Dsc(Add(X("s"), D(1))),
            Seq(Parenthesized(Dsc(X("s"))), Cup, Parenthesized(additions))));
        return VertexBinders(All(VZero, X("V"), All(X("v"), LabelType,
            And(initial, step))));
    }

    private static Formula UpperDegreeFormula()
    {
        var predicate = LambdaOf(Rho, FinsetOf(X("V")), And(
            Relation(Tau, FormulaRelationOperator.SubsetOf, Rho),
            Equal(Card(Rho), Add(Card(Tau), D(1)))));
        return VertexBinders(All(X("C"), FinsetOf(FinsetOf(X("V"))),
            All(Tau, FinsetOf(X("V")), Equal(
                Typed(At(Named("upperDegree"), X("C"), Tau), Naturals),
                Card(At(Name("Finset", "filter"), predicate, X("C")))))));
    }

    private static Formula DegreeSetFormula() => VertexBinders(
        All(X("C"), FinsetOf(FinsetOf(X("V"))), All(X("d"), Naturals,
            Equal(Typed(At(Named("degreeSet"), X("C"), X("d")), SetOf(Naturals)),
                Seq(OpenBrace, Typed(X("k"), Naturals), Sp, Mid, Sp,
                    Some(Tau, FinsetOf(X("V")), And(
                        Relation(Tau, FormulaRelationOperator.MemberOf, X("C")),
                        And(Equal(Card(Tau), Add(X("d"), D(1))),
                            Equal(At(Named("upperDegree"), X("C"), Tau), X("k"))))), CloseBrace)))));

    private static Formula ClaimFormula()
    {
        var identity = Equal(At(Named("degreeSet"), Dsc(X("n")), X("d")),
            At(Name("insert"), D(0), At(Named("degreeSet"),
                Dsc(Subtract(X("n"), X("d"))), D(0))));
        var dimensions = All(X("d"), Naturals, All(X("n"), Naturals,
            Arrow(Relation(D(1), FormulaRelationOperator.LessThanOrEqual, X("d")),
                Arrow(Relation(Add(X("d"), D(1)), FormulaRelationOperator.LessThanOrEqual, X("n")),
                    identity))));
        var avoidsRoot = All(X("s"), Naturals, All(SigmaLower, FinsetOf(X("V")),
            Relation(At(X("v"), X("s"), SigmaLower), FormulaRelationOperator.NotEqual, VZero)));
        var injective = At(Name("Function", "Injective"), At(Name("Function", "uncurry"), X("v")));
        return VertexBinders(All(VZero, X("V"), All(X("v"), LabelType,
            Arrow(injective, Arrow(avoidsRoot, dimensions)))));
    }

    private static Formula VertexBinders(Formula body) => All(X("V"), Name("Type"),
        Seq(OpenBracket, At(Name("DecidableEq"), X("V")),
            CloseBracket, Comma, Sp, Parenthesized(body)));
    private static Formula Naturals => Seq(Mathbb, Grp(X("N")));
    private static Formula VZero => new Formula.Subscript(X("v"), D(0));
    private static Formula LabelType => Arrow(Naturals, Arrow(FinsetOf(X("V")), X("V")));
    private static Formula FinsetOf(Formula type) => At(Name("Finset"), type);
    private static Formula SetOf(Formula type) => At(Name("Set"), type);
    private static Formula Dsc(Formula n) => At(Named("dsc"), VZero, X("v"), n);
    private static Formula Card(Formula value) => At(Name("Finset", "card"), value);
    private static Formula Singleton(Formula value) => Seq(OpenBrace, value, CloseBrace);
    private static Formula Named(string name) => Name(name);
    private static Formula X(string name) => F.Id(name);
    private static Formula Name(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) => Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
}
