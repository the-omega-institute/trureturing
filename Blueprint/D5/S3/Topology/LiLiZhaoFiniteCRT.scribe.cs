using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class LiLiZhaoFiniteCRTDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime-residue cylinders supply the compatibility bridge for the Li--Li--Zhao prime-tail topology construction.",
        H("Prime-tail topology bridge"),
        Blocks(
            Paragraph(Text("The underlying space is the set N of natural numbers including zero. The function primeSeq(i), abbreviated p(i), is the increasing enumeration Nat.nth Nat.Prime i, starting with p(0)=2. For natural i and a, residue(i,a) is the set of x with x congruent to a modulo p(i). For a finite set s of natural indices and an arbitrary assignment a:N to N, finiteCylinder(s,a) is the intersection of residue(i,a(i)) over i in s; the empty intersection is the whole space. No bound on the residues is needed for CRT.")),
            Entry("finite-crt", "finite_crt", "Finite Chinese-remainder compatibility",
                All("s", Supports, All("a", Assignments, Exists("x", N,
                    All("i", N, Implies(Mem(I, S), Eq(Mod(X, Prime(I)), Mod(App("a", I), Prime(I)))))))),
                "Every finite assignment of residue classes at distinct prime indices has a natural-number solution. The proof uses Mathlib's finite Chinese-remainder construction and pairwise coprimality of distinct entries of primeSeq."),
            Entry("finite-cylinder-nonempty", "finiteCylinder_nonempty", "Every finite cylinder is nonempty",
                All("s", Supports, All("a", Assignments, App("Nonempty", Cylinder(S, A)))),
                "The finite CRT solution lies in the intersection of all selected prime residue classes."),
            Entry("disjoint-cylinders-nonempty", "disjoint_cylinders_nonempty", "Disjoint supports still have a common point",
                All("s", Supports, All("t", Supports, Implies(App("Disjoint", S, T),
                    All("a", Assignments, All("b", Assignments,
                        App("Nonempty", App("inter", Cylinder(S, A), Cylinder(T, B)))))))),
                "Given disjoint finite supports and arbitrary assignments a and b, merge the assignments on their union and take a point of the resulting nonempty cylinder. Its restrictions give a common point of the two original cylinders."),
            Entry("tail-subbasis", "tailSubbasis", "Prime-tail subbases",
                All("n", N, All("U", Sets, Iff(Mem(U, App("tailSubbasis", Id("n"))),
                    Exists("i", N, And(Le(Id("n"), I), Exists("a", N,
                        And(Lt(A, Prime(I)), Eq(U, App("residue", I, A))))))))),
                "At level n the subbasis contains every residue class modulo p(i) with i at least n and representative a less than p(i). The definition tailTopology(n) is TopologicalSpace.generateFrom(tailSubbasis(n)). Increasing n removes subbasic opens, so the open-set collections decrease. In Mathlib's reverse order on topologies, n at most m gives tailTopology(n) at most tailTopology(m).",
                DescribeRole.Definition),
            Entry("tail-topology-t2", "tailTopology_t2", "Every prime-tail topology is Hausdorff",
                All("n", N, App("TTwoSpace", N, App("tailTopology", Id("n")))),
                "For distinct x and y, choose i=max(n,x+y+1). The bound i+2 at most p(i) makes x and y distinct representatives below p(i). Their singleton-support cylinders are disjoint neighborhoods, obtained from the finite-cylinder neighborhood lemma."),
            Entry("finite-cylinder-basis", "finiteCylinder_basis_of_isOpen", "Finite cylinders form local basic neighborhoods",
                All("n", N, All("U", Sets, Implies(App("IsOpen", App("tailTopology", Id("n")), U),
                    All("x", N, Implies(Mem(X, U), Exists("s", Supports, Exists("a", Assignments,
                        And(All("i", N, Implies(Mem(I, S), Le(Id("n"), I))),
                            And(All("i", N, Implies(Mem(I, S), Lt(App("a", I), Prime(I)))),
                                And(Mem(X, Cylinder(S, A)), Subset(Cylinder(S, A), U))))))))))),
                "For every open U at level n and every x in U there is a finite cylinder through x, contained in U, with all support indices at least n and all representatives below their prime moduli. Induction on generated opens handles basic sets, the whole space, intersections, and arbitrary unions. In an intersection, the common point forces the two representatives to agree wherever the supports overlap. This explicit support-and-representative extraction is the local bridge used in the irreducibility proof.",
                provenance: AssessedProvenance.FromRepo()),
            Paragraph(Text("The definition commonTopology is the Mathlib supremum iSup n (tailTopology n). Precisely, commonTopology_isOpen_iff says that a set is open in commonTopology if and only if it is open in every tailTopology(n). Mathlib orders topologies by reverse inclusion of their open sets. Thus this supremum is the intersection, or infimum in the paper's inclusion order, of the tail open-set collections. IsOpen(T,U) below uses the displayed topology T; TOneSpace, TTwoSpace and QuasiSober likewise carry the displayed topology explicitly.")),
            Entry("common-t1", "commonTopology_t1", "The common topology is T1",
                App("TOneSpace", N, Common),
                "Every singleton is closed in each Hausdorff tail topology. Closed singletons persist in the intersection of the tail open-set collections, which is Mathlib's supremum."),
            Entry("common-irreducible", "commonTopology_univ_irreducible", "The whole space is irreducible in the common topology",
                App("IsIrreducible", Common, App("univ", N)),
                "Given two nonempty common opens U and V, take a finite cylinder contained in U at level zero, with support s. The cutoff m=sum(s)+1 is greater than every index in s, including the empty-support case. Take a cylinder contained in V at level m. Its support is disjoint from s, so CRT compatibility gives a point in U and V. The whole space is nonempty, hence irreducible and closed."),
            Entry("common-not-quasi-sober", "commonTopology_not_quasiSober", "The common topology is not quasi-sober",
                F.Seq(F.Neg, F.Sp, App("QuasiSober", N, Common)),
                "Quasi-sobriety would give the whole irreducible closed space a generic point x. T1 makes the closure of the singleton x equal to that singleton; the natural number x+1 shows that it is smaller than the whole space. Thus even existence of a generic point fails, and in particular the space is not sober."),
            Paragraph(Text("These are the prime-tail topologies of Li--Li--Zhao, Sober topologies on a set, Example 3.9. Their underlying N-zero is Lean's N. Their prime p(k), indexed from 1, is primeSeq(k-1); their tail at index n+1 is tailTopology(n). This reindexing preserves every tail and their common-open topology. Their meet is our Mathlib supremum, by the order convention above. The construction proves every tail Hausdorff and the common topology T1, irreducible on the whole space, and non-quasi-sober. No claim about the separate cofinite-topology comparison in Remark 3.10 is included.")))));

    private static ScribeNode Entry(string id, string name, string title, Formula statement,
        string proof, DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Topology/LiLiZhaoFiniteCRT." + name),
            H(title), StatementSource.FromAuthor(F.Disp(statement)), provenance ??
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/lilizhao2025sober")),
            Blocks(Paragraph(Text(proof))), role);

    private static Formula Id(string value) => F.Id(value);
    private static Formula N => F.Seq(F.Mathbb, F.Grp(Id("N")));
    private static Formula Supports => App("Finset", N);
    private static Formula Sets => App("Set", N);
    private static Formula Assignments => F.Seq(N, F.To, F.Sp, N);
    private static Formula I => Id("i");
    private static Formula X => Id("x");
    private static Formula U => Id("U");
    private static Formula S => Id("s");
    private static Formula T => Id("t");
    private static Formula A => Id("a");
    private static Formula B => Id("b");
    private static Formula Common => Id("commonTopology");
    private static Formula App(string name, params Formula[] args)
    {
        var parts = new List<Formula> { F.Operatorname, F.Grp(Id(name)), F.Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i != 0) parts.Add(F.Comma);
            parts.Add(args[i]);
        }
        parts.Add(F.Close);
        return F.Seq([.. parts]);
    }
    private static Formula Prime(Formula i) => App("primeSeq", i);
    private static Formula Cylinder(Formula s, Formula a) => App("finiteCylinder", s, a);
    private static Formula Mod(Formula x, Formula p) => App("mod", x, p);
    private static Formula All(string name, Formula type, Formula body) =>
        F.Seq(F.Forall, F.Sp, Id(name), F.Colon, type, F.Comma, F.Sp, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        F.Seq(F.Exists, F.Sp, Id(name), F.Colon, type, F.Comma, F.Sp, body);
    private static Formula Binary(Formula a, Formula op, Formula b) => F.Seq(F.Open, a, op, F.Sp, b, F.Close);
    private static Formula And(Formula a, Formula b) => Binary(a, F.Land, b);
    private static Formula Implies(Formula a, Formula b) => Binary(a, F.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Binary(a, F.Iff, b);
    private static Formula Eq(Formula a, Formula b) => Binary(a, F.Eq, b);
    private static Formula Le(Formula a, Formula b) => Binary(a, F.Le, b);
    private static Formula Lt(Formula a, Formula b) => Binary(a, F.Lt, b);
    private static Formula Mem(Formula a, Formula b) => Binary(a, F.InMacro, b);
    private static Formula Subset(Formula a, Formula b) => Binary(a, F.Subseteq, b);
}
