using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA300591FixedAssembliesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA300591FixedAssemblies.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/hanna2018a300591");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invariant assemblies of ordered decorated blocks split into their fixed and moved parts, " +
        "with an exact product formula for arbitrary integer block weights.",
        H("Fixed and moved blocks in Hanna's signed assemblies"), Blocks(
            Describe.Lean(DescribeId.Create("hannaa300591-fixed-assembly-weight-factorization"),
                DeclarationHandle.Create(Prefix + "fixed_assembly_weight_factorization"),
                H("The signed fixed-assembly factorization"),
                StatementSource.FromAuthor(Disp(All("V", Call("FiniteTypes"),
                    All("C", Call("FiniteTypes"),
                    All("allowed", Call("Predicate", N(), V("C")),
                    All("S", Call("Finset", V("V")),
                    All("T", Call("Finset", V("V")),
                    All("g", Call("Perm", V("V")),
                    All("sign", Call("Function", V("C"), Z()),
                        Eqn(Call("fixedSum", V("allowed"), V("S"), V("T"), V("g"), V("sign")),
                            Mul(Call("assemblySum", V("allowed"),
                                    Call("Fix", V("g"), V("S")), Call("Fix", V("g"), V("T")), V("sign")),
                                Call("fixedSum", V("allowed"), Call("Moved", V("g"), V("S")),
                                    V("T"), V("g"), V("sign"))))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Let V and C be arbitrary finite types, with decidable equality, and let " +
                    "allowed(j,c) be any predicate on block sizes and colors. A block is a " +
                    "nonempty list of distinct vertices, a color c, and an ordered pair of " +
                    "ambient markers; the two markers may coincide. An assembly on S with " +
                    "markers in T is an unordered finite set of these decorated blocks. " +
                    "The vertex lists are pairwise disjoint, cover exactly S, and satisfy " +
                    "allowed(length,c). Relabeling by g preserves the block order and color " +
                    "and applies g to every vertex and both markers. FixedAssembly consists " +
                    "of assemblies closed under this relabeling. The weight of an assembly " +
                    "is the product of sign(c) over its blocks; sign may be any integer-valued " +
                    "function, so negative and zero weights are included. The notation " +
                    "assemblySum means the sum of these weights over all assemblies, " +
                    "and fixedSum means the sum over invariant assemblies. Fix(g,S) is " +
                    "the subset of S fixed by g; Moved(g,S) is its complement within S.")),
                    Paragraph(Text(
                    "If an invariant assembly has a block containing a fixed vertex, its " +
                    "relabeling shares that vertex with the original block. Disjointness " +
                    "forces equality of the decorated blocks. Equality of their ordered " +
                    "lists forces every vertex of the block to be fixed, and equality of " +
                    "their two markers forces both markers to be fixed. Thus a block cannot " +
                    "mix fixed and moved vertices. Restricting to the two kinds of block " +
                    "gives an equivalence; its inverse is disjoint union. The moved part " +
                    "retains the original marker set T. Multiplicativity of the weight " +
                    "under this disjoint union gives the displayed identity.")),
                    Paragraph(Text(
                    "No stability assumption on S or T is required, and the empty fixed " +
                    "or moved set is included. Taking S=T=V gives the unpointed fixed " +
                    "assembly split. Taking S=V with one fixed distinguished vertex removed " +
                    "and T=V preserves the ambient markers for the pointed subtraction term. " +
                    "Size restrictions and finite signed color sets can be expressed by allowed. " +
                    "HannaA300591AssemblyCoefficients identifies the assembly sums with " +
                    "ordinary exponential coefficients and realizes every integer strict prefix " +
                    "by a finite signed palette. That module also proves the actual actions, " +
                    "signed Burnside identity and Sylow arithmetic, which are used by the " +
                    "all-degree source induction in HannaA300591RationalModel."))),
                DescribeRole.Theorem), RecursionBlock())));

    private static DocumentBlock RecursionBlock() =>
        Describe.Lean(DescribeId.Create("hannaa300591-assembly-weight-point-recursion"),
            DeclarationHandle.Create(Prefix + "assembly_weight_point_recursion"),
            H("Removing the block at a chosen vertex"),
            StatementSource.FromAuthor(Disp(All("V", Call("FiniteTypes"),
                All("C", Call("FiniteTypes"),
                All("allowed", Call("Predicate", N(), V("C")),
                All("S", Call("Finset", V("V")),
                All("T", Call("Finset", V("V")),
                All("x", V("S"), All("sign", Call("Function", V("C"), Z()),
                    Eqn(Call("assemblySum", V("allowed"), V("S"), V("T"), V("sign")),
                        Call("rootSum", V("allowed"), V("S"), V("T"), V("x"), V("sign")))))))))))),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "For any chosen x in S, RootBlock consists of the allowed decorated " +
                "blocks b whose list contains x, whose vertices belong to S, and whose " +
                "two markers belong to T. The expression rootSum is the sum over b of " +
                "sign(color(b)) times assemblySum on S with the vertices of b removed, " +
                "with the same marker set T. The theorem equates this expression with " +
                "the signed sum over all assemblies on S. There is no permutation " +
                "invariance hypothesis in this recurrence.")),
                Paragraph(Text(
                "Disjointness and coverage give a unique block containing x. Remove it " +
                "to obtain an assembly on the remaining vertices. Conversely, insert " +
                "any admissible root block into an assembly on its complementary support. " +
                "The complementary support prevents the root block from already occurring. " +
                "These operations are inverse, and inserting the block multiplies the " +
                "assembly weight by its color weight. Summing over the resulting dependent " +
                "pairs proves the recurrence. HannaA300591AssemblyCoefficients evaluates " +
                "the root-block sum by support, order, color and ambient marker pair, " +
                "then proves that this recurrence agrees with the exponential derivative " +
                "recurrence. The coefficient identity is proved there without an extra " +
                "counting assumption."))),
            DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
}
