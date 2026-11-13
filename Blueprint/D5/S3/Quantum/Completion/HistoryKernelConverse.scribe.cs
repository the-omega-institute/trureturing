using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class HistoryKernelConverseDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/HistoryKernelConverse.";
    private static Formula All(Formula a, Formula t, Formula b) =>
        Seq(Forall, Sp, a, Colon, Sp, t, Comma, Sp, b);
    private static Formula Ex(Formula a, Formula t, Formula b) =>
        Seq(Exists, Sp, a, Colon, Sp, t, Comma, Sp, b);
    private static Formula X => F.Id("X");
    private static Formula K => F.Id("K");
    private static Formula L => F.Id("L");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, Open, b, Close);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Sp, Land, Sp, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Iff(Formula a, Formula b) => Seq(a, Sp, Leftrightarrow, Sp, b);
    private static Formula Law => Call("KernelExtensionLaw", K);
    private static Formula PSD(Formula a) => Call("PosSemidef", a);
    private static Formula Frame(Formula body) =>
        All(X, F.Id("Type"), All(K, Arrow(X, Arrow(X, C)), body));
    private static Formula History(Formula n, Formula l) => Call("CertifiedHistory", K, n, l);
    private static Formula Cover => Call("CertifiedFiniteCover", K);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive primitive history kernel admits singular square-residual extensions; finite-set coverage by certified chains is sufficient for the universal law.",
        H("Singular History Extensions and Certified Finite Covers"),
        Blocks(
            Entry("history-finite-positivity-equivalence", "extensionLaw_iff_finiteGram_posSemidef",
                "All ordered finite tables characterize the extension law",
                Frame(Iff(Law, All(F.Id("n"), N, All(L, Arrow(Fin(F.Id("n")), X),
                    PSD(Call("finiteGram", K, L)))))),
                "The forward implication uses HistoryKernelExtension.extensionLaw_finiteGram_posSemidef. For the reverse, the actual appended Gram table is positive. Its cross-column lies in the range of its old block, even when that block is singular. Choose c with b = Gc, and apply positive congruence to the column (-c,1). The resulting scalar is the actual difference d - conjugate-transpose(c)Gc, so it is real and nonnegative. Its nonnegative real square root, embedded in the complex numbers, gives r. Hermitian symmetry then supplies the original lower cross-block, and the resulting equality retains all four actual blocks.",
                DescribeRole.Theorem),
            Entry("history-global-positivity-equivalence", "extensionLaw_iff_kernel_posSemidef",
                "The global positive form characterizes the extension law",
                Frame(Iff(Law, PSD(K))),
                "For an arbitrary label type, Matrix.PosSemidef includes Hermitian symmetry and positivity on finitely supported coefficient families. Its finite restrictions give every ordered Gram table, with repeated labels allowed. In the other direction the existing forward theorem supplies the global positive form. This equivalence is used to recover the extension law from certified finite covers.",
                DescribeRole.Theorem),
            Entry("history-local-chain-certificate", "CertifiedHistory",
                "A certificate starts at the empty table and retains each extension equality",
                CertificateFormula(),
                "The zero-length certificate is True. For a successor list, tail(L)(i) = L(i.succ) is certified and the actual Sum.elim table appending L(0) to that tail equals residualExtension of the tail table for some c and r. Reindexing puts the newly appended Unit coordinate at index zero of the given list. This records an actual sequence of the primitive block equalities; no positivity premise is inserted.",
                DescribeRole.Definition),
            Entry("history-certified-finite-cover", "CertifiedFiniteCover",
                "Every finite label set is contained in a certified history",
                Frame(Eq(Cover, CoverFormula())),
                "Each finite set may have its own certified chain. The certificate may contain extra labels and repeats. There is no assumption of one countable log covering the entire label type.",
                DescribeRole.Definition),
            Entry("history-covered-chains-extension", "certifiedFiniteCover_extensionLaw",
                "A certified finite cover supplies the universal extension law",
                Frame(Imp(Cover, Law)),
                "Induction on each individual certificate proves positivity of its actual terminal table, using the original residual-extension positivity lemma. Given any ordered finite list, take a certified chain covering its label set and choose a position for each requested label. Pullback of the terminal table gives the requested Gram table, including repeated requested labels. The finite-support positive-form supplier then yields the global positive kernel, and the preceding equivalence supplies every same-entry extension witness.",
                DescribeRole.Theorem),
            FiniteComparisonApplication(),
            Paragraph(Text(
                "The block range and finite-support suppliers are adapted from TauCetiProject/TauCeti at revision 52f9d081237dadaf6d4eae13629281f7faa37d54, specifically LinearAlgebra/Matrix/PosSemidef.lean and Analysis/Matrix/PosSemidef/Block.lean. They implement standard positive block matrix facts. All results allow empty index types, singular and zero old blocks, zero diagonals and zero residuals. When the history type is empty, the extension obligation has no appended label and is vacuous.")),
            Paragraph(Text(
                "Certification of a single log only establishes positivity for its represented labels; the finite-cover quantifier is essential for a conclusion on the whole declared label type. The label-preserving minimal Hilbert representation and its uniqueness require the separate completion argument. No CP, Born, physical control or empirical realization follows from the kernel equivalences alone.")))));

    private static DocumentBlock FiniteComparisonApplication() =>
        new DocumentBlock.Section(H("Application: a single finite-test schema"), Blocks(
            Paragraph(Text("For an arbitrary finite complex table M, define its entire quadratic evaluation Q_M(z)=sum_{i,j} conjugate(z_i) M_{ij} z_j. If Q_M(z) is real for every complex coefficient vector z, M is Hermitian. If Q_M(z) is real and nonnegative for every z, M is positive semidefinite. Reality of the whole complex value is essential: a nonnegative real part alone does not suffice. For example M=[i] passes that real-part inequality for every z, but M is not Hermitian.")),
            new DocumentBlock.DisplayFormula(FiniteEvaluationFormula()),
            Paragraph(Text("These implications directly reuse Mathlib LinearMap.isSymmetric_iff_inner_map_self_real and LinearMap.isPositive_iff_complex through Matrix.isSymmetric_toEuclideanLin_iff and Matrix.isPositive_toEuclideanLin_iff. The first implication supplies endpoint conjugation instead of assuming it as a separate clause. The test already presupposes complex-valued entries and arbitrary complex coefficient vectors; it does not derive the complex field or an operational superposition mechanism.")),
            Paragraph(Text("For one common kernel K on the entire label type, impose this same evaluation condition on every finite ordered label family and every complex coefficient vector. The resulting positive finiteGram tables give KernelExtensionLaw through extensionLaw_iff_finiteGram_posSemidef. Repeated labels and empty families remain allowed. The universal schema is not one finite experiment, and separately chosen tables cannot substitute for restrictions of the same K. A label-preserving Hilbert realization still uses the separate common-kernel completion construction, such as RKHS.OfKernel; these finite tests do not themselves specify physical operations.")),
            Paragraph(Text("Two-label legality alone is insufficient. The real symmetric three-label table with diagonal 1 and every off-diagonal -1 has positive semidefinite two-label restrictions, including repeated-label restrictions. At z=(1,1,1), its entire quadratic evaluation is -3, so the three-label table is not positive semidefinite. Pairwise comparisons therefore do not settle simultaneous finite consistency.")),
            Paragraph(Text("Counting clauses does not show that raw complex positivity is logically weaker than the original three-way characterization: their objects and premises differ. Endpoint reversal K(y,x)=conjugate(K(x,y)) is also distinct from reversing a sequence of measurements. No commutation of measurement updates, operational preparations, Born interpretation, tensor composition, or dynamics follows here.")),
            Paragraph(Text("白话：每两项单独看都合法，放到一起仍可能矛盾。更准确的简洁要求是：同一张比较表的每个有限部分，对所有复系数作整体检验都得到非负实数；反向比较的共轭关系会随之成立。这是一条普遍检验规则，不是一次有限实验，也还不是量子力学的完整起源。"))));

    private static Formula FiniteEvaluationFormula()
    {
        var m = F.Id("M"); var z = F.Id("z");
        var q = Call("quadraticEvaluation", m, z);
        var re = Call("Re", q);
        var real = Eq(Call("ofReal", re), q);
        return All(z, Arrow(F.Id("I"), C), And(real, Seq(D(0), Sp, Le, Sp, re)));
    }

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string narrative, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))), role);

    private static Formula CoverFormula()
    {
        Formula s = F.Id("s"), n = F.Id("n"), x = F.Id("x"), i = F.Id("i");
        return All(s, Call("Finset", X), Ex(n, N, Ex(L, Arrow(Fin(n), X),
            And(History(n, L), All(x, X,
                Imp(Seq(x, Sp, InMacro, Sp, s), Ex(i, Fin(n), Eq(Call("L", i), x))))))));
    }

    private static Formula CertificateFormula()
    {
        Formula n = F.Id("n"), c = F.Id("c"), r = F.Id("r");
        Formula zero = All(L, Arrow(Fin(D(0)), X), Eq(History(D(0), L), Call("True")));
        Formula next = Seq(n, Sp, Plus, Sp, D(1));
        Formula tail = Call("tail", L);
        Formula step = All(n, N, All(L, Arrow(Fin(next), X),
            Eq(History(next, L), And(History(n, tail),
                Ex(c, Call("Matrix", Fin(n), Call("Unit"), C), Ex(r, C,
                    Eq(Call("finiteGram", K, Call("append", tail, Call("head", L))),
                        Call("residualExtension", Call("finiteGram", K, tail), c, r))))))));
        return Frame(And(zero, step));
    }
}
