using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class NikiforovConjecture442RefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/nikiforov2016beyondgraphenergy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The equality criterion in Nikiforov's Conjecture 4.42 fails for a complex tripartite matrix.",
        H("Entrywise modulus does not determine a Schatten norm"),
        Blocks(
            Describe.Lean(DescribeId.Create("nikiforov-partite"), DeclarationHandle.Create(Module + ".rPartite"),
                H("Nonempty common index parts"),
                StatementSource.FromAuthor(Disp(PartiteDefinition())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The same surjective coloring is used on rows and columns. Its fibers are "
                    + "nonempty, pairwise disjoint and cover the index set. The private parts_iff bridge proves "
                    + "equivalence with a family of r nonempty finite sets, unique part membership and zero "
                    + "entries within every common part. No restriction is imposed on entries between parts."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nikiforov-turan"), DeclarationHandle.Create(Module + ".turanMatrix"),
                H("The canonical complex Turán adjacency"),
                StatementSource.FromAuthor(Disp(TuranDefinition())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The graph is the pinned Mathlib SimpleGraph.turanGraph n r; vertices i and j "
                    + "are adjacent exactly when their residues modulo r differ. Its adjacency matrix has complex "
                    + "entries zero and one. For n ≥ r > 0 this is a complete graph between r nonempty balanced "
                    + "parts. The balanced_relabel bridge uses Finpartition.IsEquipartition.exists_partPreservingEquiv "
                    + "to represent every balanced finite partition by a simultaneous relabeling. The converse "
                    + "in modulus_partition_iff uses the graph's Turán-maximal partition, including its cardinality "
                    + "and equipartition laws."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nikiforov-modulus"), DeclarationHandle.Create(Module + ".isTuranModulus"),
                H("The source equality condition"),
                StatementSource.FromAuthor(Disp(ModulusDefinition())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The norm of each complex entry is embedded back into the complex numbers. "
                    + "A single permutation acts on both indices. The modulus_partition_iff bridge identifies this "
                    + "condition with adjacency across the parts of an arbitrary equipartition into r nonempty "
                    + "parts. Permuting vertices preserves the Schatten norm: schatten_reindex compares column-Gram "
                    + "characteristic polynomials and the ordered Hermitian eigenvalue lists, so balanced_norm "
                    + "also proves that the comparison graph's labeling is immaterial."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nikiforov-full-claim"), DeclarationHandle.Create(Module + ".claim"),
                H("Conjecture 4.42 in full"),
                StatementSource.FromAuthor(Disp(Equal(Named("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Nikiforov, Beyond graph energy: norms of graphs and matrices, "
                    + "arXiv:1510.02850v2, §4.5.1, Conjecture 4.42: Let p > 2, n ≥ r ≥ 2, and let A be an "
                    + "n × n complex matrix with max-norm at most one. If A is r-partite, its Schatten p-norm "
                    + "is at most that of T_r(n). Equality holds if and only if the entrywise absolute-value "
                    + "matrix is the adjacency matrix of T_r(n).")),
                    Paragraph(Text("The formula retains the universal real exponent, both integer inequalities, "
                    + "all complex square matrices, every entry bound, multipartiteness, the upper bound and both "
                    + "directions of the equality criterion. Symmetry, Hermitianity and nonnegativity are absent. "
                    + "For n ≥ r ≥ 2 the index set is nonempty; max_bound_iff equates the pointwise bound with "
                    + "the maximum over all pairs of indices. Here S(p,A) denotes the public "
                    + "UpperBranchReduction.schattenNorm p A, the p-th root of the finite sum of singular-value "
                    + "p-th powers. Its schattenPow_eq_columnGram bridge includes zero eigenvalues. "
                    + "The source_equality bridge transports the sufficiency direction to any balanced partition "
                    + "without changing the matrix domain or the exponent."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nikiforov-refutation"), DeclarationHandle.Create(Module + ".result"),
                H("A three by three counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take p = 6, n = r = 3 and A = [[0,1,1],[-1,0,1],[-1,-1,0]]. "
                    + "Singleton parts certify multipartiteness and the identity permutation identifies its "
                    + "entrywise modulus with T_3(3). The public schattenPow_trace formula reduces the sixth-power "
                    + "sum to Re(trace((Aᴴ A)^3)), using cfc_pow_id on the Hermitian column Gram matrix. "
                    + "Exact finite arithmetic gives 54 for A and 66 for T_3(3). Equality sufficiency would "
                    + "equate their Schatten 6-norms; schattenNorm_rpow would then give 54 = 66.")),
                    Paragraph(Text("The result negates the entire universal conjunction, through failure of "
                    + "equality sufficiency. The upper-bound-only proposition remains unresolved by this argument. "
                    + "No claim is made about a p = 3 obstruction, dimension minimality or a Hadamard family. "
                    + "The source provides the conjecture; the counterexample and formal derivation are "
                    + "repository results. The bounded literature screen does not establish global novelty."))),
                DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        var p = F.Id("p"); var n = F.Id("n"); var r = F.Id("r"); var a = F.Id("A");
        var i = F.Id("i"); var j = F.Id("j");
        var bounded = All(i, Fin(n), All(j, Fin(n), LE(Norm(App(a, i, j)), D(1))));
        var lhs = Call("S", p, a); var rhs = Call("S", p, Call("turanMatrix", n, r));
        var conclusion = And(LE(lhs, rhs), Iff(Equal(lhs, rhs), Call("isTuranModulus", r, a)));
        return All(p, Reals(), Imp(LT(D(2), p), All(n, Naturals(), All(r, Naturals(),
            Imp(LE(D(2), r), Imp(LE(r, n), All(a, Mat(n),
                Imp(bounded, Imp(Call("rPartite", r, a), conclusion)))))))));
    }

    private static Formula PartiteDefinition()
    {
        var n = F.Id("n"); var r = F.Id("r"); var a = F.Id("A"); var c = F.Id("c");
        var i = F.Id("i"); var j = F.Id("j");
        var body = Ex(c, new Formula.TypeArrow(Fin(n), Fin(r)),
            And(Call("Surjective", c), All(i, Fin(n), All(j, Fin(n),
                Imp(Equal(App(c, i), App(c, j)), Equal(App(a, i, j), D(0)))))));
        return All(n, Naturals(), All(r, Naturals(), All(a, Mat(n),
            Equal(Call("rPartite", r, a), body))));
    }

    private static Formula TuranDefinition()
    {
        var n = F.Id("n"); var r = F.Id("r");
        return All(n, Naturals(), All(r, Naturals(), Equal(Call("turanMatrix", n, r),
            App(Seq(Parenthesized(Call("SimpleGraphTuranGraph", n, r)), Dot, Named("adjMatrix")), Complexes()))));
    }

    private static Formula ModulusDefinition()
    {
        var n = F.Id("n"); var r = F.Id("r"); var a = F.Id("A"); var e = F.Id("e");
        var i = F.Id("i"); var j = F.Id("j");
        var body = Ex(e, Call("EquivPerm", Fin(n)), All(i, Fin(n), All(j, Fin(n),
            Equal(Call("ofReal", Norm(App(a, i, j))), Call("turanMatrix", n, r, App(e, i), App(e, j))))));
        return All(n, Naturals(), All(r, Naturals(), All(a, Mat(n),
            Equal(Call("isTuranModulus", r, a), body))));
    }

    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), Complexes());
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(Formula v, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(v, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(Formula v, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(v, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Equality(x, y);
    private static Formula And(Formula x, Formula y) => new Formula.And(Parenthesized(x), Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Implies(Parenthesized(x), Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Longleftrightarrow, Sp, Parenthesized(y));
    private static Formula LE(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessOrEqual, y);
    private static Formula LT(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
}
