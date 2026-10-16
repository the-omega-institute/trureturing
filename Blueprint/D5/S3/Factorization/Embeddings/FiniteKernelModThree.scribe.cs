using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;
internal sealed class FiniteKernelModThreeDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => FormulaDsl.Id(s);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string v, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), t, b);
    private static Formula Q(Formula a) => Call("ModN", a, Num(3));
    private static Formula Rank(Formula r, Formula a) => Call("finrank", r, a);
    private static DocumentBlock Entry(string n, string h, Formula f, string p) =>
        Describe.Lean(DescribeId.Create(n.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Factorization/Embeddings/FiniteKernelModThree." + n),
            H(h), StatementSource.FromAuthor(f), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(p))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite kernels preserve the original quotient by triples and bound embedded unit cube classes.",
        H("Finite-kernel descent for cube classes"), Blocks(
            Paragraph(Text("Let A and L be additive commutative groups and f:A->L a surjective "
                + "homomorphism with finite kernel. Assume 3a=0 implies a=0 for every a in A. "
                + "ModN(A,3) is Mathlib's quotient A/3A, with its standard ZMod(3) module structure. "
                + "Multiplication by three is injective on the finite kernel, hence surjective there. "
                + "If f(a)=3l, lift l to v and solve 3t=a-3v inside the kernel. Then a=3(v+t) "
                + "inside A. Thus the induced map A/3A -> L/3L is an equivalence. "
                + "For finite free L, Mathlib's ModN.basis supplies all coordinate reduction.")),
            Entry("modThree_finite_finrank", "Finite free image determines the cube quotient dimension",
                All("A", I("AddCommGroup"), All("L", I("AddCommGroup"),
                    All("f", Call("AddHom", I("A"), I("L")),
                        Imp(Call("FiniteKernelDescentHypotheses", I("A"), I("L"), I("f")),
                            And(Call("ModuleFinite", Call("ZMod", Num(3)), Q(I("A"))),
                                Equal(Rank(Call("ZMod", Num(3)), Q(I("A"))),
                                    Rank(I("Int"), I("L")))))))),
                "FiniteKernelDescentHypotheses denotes exactly the preceding group, surjectivity, "
                + "finite-kernel and no-three-torsion hypotheses, together with L finite free over Int. "
                + "The equivalence transfers finite dimensionality and the reduced integral basis "
                + "computes the dimension."),
            Entry("embedded_units_modThree", "Original unit cube quotients satisfy the Dirichlet bound",
                All("K", I("NumberField"), All("U", I("CommGroup"),
                    All("i", Call("MonoidHom", I("U"), Call("Units", Call("Integers", I("K")))),
                        Imp(Call("EmbeddedUnitHypotheses", I("K"), I("U"), I("i")),
                            And(Call("ModuleFinite", Call("ZMod", Num(3)), Q(Call("Additive", I("U")))),
                                new Formula.Relation(Rank(Call("ZMod", Num(3)), Q(Call("Additive", I("U")))),
                                    FormulaRelationOperator.LessThanOrEqual,
                                    Call("UnitRank", I("K")))))))),
                "Here K is any number field, U any commutative group, i:U->Units(O(K)) injective, "
                + "and u^3=1 implies u=1 in U. These are all the EmbeddedUnitHypotheses. "
                + "DirichletUnitCompletion splits integer units into finite torsion and a free lattice. "
                + "Restrict the free coordinate to its actual image L. Its kernel injects into the "
                + "finite torsion group; L is a finite free integral submodule. Finite-kernel descent "
                + "then bounds the dimension by the ambient Dirichlet rank. An embedding of groups "
                + "alone does not imply an embedding of cube quotients: the inclusion 3Int->Int "
                + "sends a nonzero cube class to zero. The kernel correction supplies cube witnesses "
                + "in U itself. The consumed helper exists_original_cube_of_quotient_eq takes "
                + "equality of two classes in ModN(Additive(U),3) and returns w in the same U "
                + "with u=v*w^3. ResetQ4UnitCubes uses it for both original-order normal forms; "
                + "it is quotient-kernel witness extraction, not a separate content result."))));
}
