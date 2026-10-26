using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class BipartiteDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => F.Id(s);
    private static Formula C => Seq(Mathbb, Grp(I("C")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(
        s.Contains('.') ? Seq(I(s.Split('.')[0]), Dot, I(s.Split('.')[1])) : I(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula p) =>
        Seq(Forall, Sp, Par(Seq(I(s), Colon, t)), Comma, Sp, p);
    private static Formula Eq(Formula a, Formula b) => Seq(a, F.Eq, b);
    private static Formula Mul(Formula a, Formula b) => Par(Seq(a, Cdot, Sp, b));
    private static Formula J => Par(Seq(I("A"), Times, Sp, I("B")));
    private static Formula Mat => Call("Matrix", J, J, C);
    private static Formula Systems(Formula p) => All("A", I("Type"), All("B", I("Type"), p));
    private static Formula Instance(string s, string t) =>
        Seq(OpenBracket, Call(s, I(t)), CloseBracket, Sp);
    private static Formula TransposeDefinition() => Systems(All("M", Mat,
        All("p", J, All("q", J, Eq(Call("partialTranspose", I("M"), I("p"), I("q")),
            Call("M", Call("Prod.mk", Call("Prod.fst", I("p")), Call("Prod.snd", I("q"))),
                Call("Prod.mk", Call("Prod.fst", I("q")), Call("Prod.snd", I("p")))))))));
    private static Formula ApptDefinition()
    {
        var u = Call("val", I("U"));
        var conjugate = Mul(Mul(u, I("M")), Call("Matrix.conjTranspose", u));
        return Systems(Seq(Instance("Fintype", "A"), Instance("Fintype", "B"),
            Instance("DecidableEq", "A"), Instance("DecidableEq", "B"),
            All("M", Mat, Seq(Call("APPT", I("M")), Iff, Sp,
                All("U", Call("unitaryGroup", J, C),
                    Call("Matrix.PosSemidef", Call("partialTranspose", conjugate)))))));
    }
    private static DocumentBlock Desc(string name, string title, Formula f, string prose) =>
        Describe.Lean(DescribeId.Create("appt-bipartite-" + name.ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite." + name),
            H(title), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared product-matrix primitives preserve the existing second-factor transpose and universal APPT meanings.",
        H("Generic bipartite matrix primitives"), Blocks(
            Paragraph(Text("Second-factor partial transpose acts on matrices indexed by a product of local types. APPT requires positivity after every global unitary conjugation. These definitions enter the dimension-general contraction decomposition and the five-row attaining family.")),
            Desc("partialTranspose", "Second-factor partial transpose", TransposeDefinition(),
                "For arbitrary local index types A and B, the output entry at ((a,b),(c,d)) is the input entry at ((a,d),(c,b)). No finiteness, decidable equality, equal-cardinality, Hermitian or positivity assumption is imposed. The operation is definitionally equal to KickedIsingNegativityRefutation.partialTranspose over the same Type-star telescope."),
            Desc("APPT", "All-unitary partial-transpose positivity", ApptDefinition(),
                "For every pair of finite local types with Fintype and DecidableEq instances, APPT M says that the second-factor partial transpose of U M U-adjoint is positive semidefinite for every global unitary on A times B. Empty and unequal local dimensions remain admitted. The Type-star telescope and full unitary group are exactly those of QutritPerturbationAttainment.APPT, which is definitionally equal to this predicate. ContractionAttainment.contraction_appt and five_row_attainment use this predicate."))));
}
