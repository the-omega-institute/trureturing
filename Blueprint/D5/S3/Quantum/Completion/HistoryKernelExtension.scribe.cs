using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class HistoryKernelExtensionDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/HistoryKernelExtension.";
    private static Formula All(Formula a, Formula t, Formula b) =>
        Seq(Forall, Sp, a, Colon, Sp, t, Comma, Sp, b);
    private static Formula X => F.Id("X");
    private static Formula K => F.Id("K");
    private static Formula L => F.Id("L");
    private static Formula I => F.Id("I");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Type => F.Id("Type");
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Kernel => Arrow(X, Arrow(X, C));
    private static Formula Gram => Call("finiteGram", K, L);
    private static Formula Law => Call("KernelExtensionLaw", K);
    private static Formula Matrix(Formula a, Formula b) => Call("Matrix", a, b, C);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula PSD(Formula a) => Call("PosSemidef", a);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Star(Formula a) => Seq(a, Caret, Grp(F.Star));
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, b);
    private static Formula Frame(Formula body) => All(X, Type, All(K, Kernel, body));
    private static Formula Ex(Formula a, Formula t, Formula body) =>
        Seq(Exists, Sp, a, Colon, Sp, t, Comma, Sp, body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed primitive kernel with universal square-residual extensions has positive finite tables and a positive free formal span.",
        H("History Kernel Extension"),
        Blocks(
            Entry("history-finite-gram", "finiteGram", "The same kernel on every indexed list",
                Frame(All(I, Type, All(L, Arrow(I, X),
                    All(F.Id("i"), I, All(F.Id("j"), I,
                        Eq(Call("finiteGram", K, L, F.Id("i"), F.Id("j")),
                            Call("K", Call("L", F.Id("i")), Call("L", F.Id("j"))))))))),
                "The label type is arbitrary. The list need not be injective; repeated labels read identical entries of the same fixed K.",
                DescribeRole.Definition),
            Entry("history-residual-extension", "residualExtension", "The complete extension block",
                ExtensionFormula(),
                "All four blocks are retained: G, Gc, conjugate-transpose(c)G, and conjugate-transpose(c)Gc plus conjugate(r)r. The index type is finite and may be empty. G may be singular and r may be zero.",
                DescribeRole.Definition),
            Entry("history-kernel-law", "KernelExtensionLaw", "The primitive universal extension law",
                Frame(Eq(Law, LawFormula())),
                "For every natural n, every ordered n-label list L and every appended label h, some c and complex r give the displayed block equality. Sum.elim appends one Unit-indexed label while preserving every old entry. No symmetry, positivity, distinctness, vector space or nonzero residual is assumed.",
                DescribeRole.Definition),
            Entry("history-all-finite-positive", "extensionLaw_finiteGram_posSemidef",
                "The extension law implies positivity on every finite list",
                Frame(Imp(Law, All(F.Id("n"), N,
                    All(L, Arrow(Fin(F.Id("n")), X), PSD(Gram))))),
                "Induction starts with the empty table. The successor step applies the actual law for K and uses the positive congruence of the old block and the scalar square. A reindexing recovers the given ordered list. Scalar Gram positivity and congruence are reused from Matrix.posSemidef_conjTranspose_mul_self and Matrix.PosSemidef.conjTranspose_mul_mul_same. This theorem is consumed by extensionLaw_kernel_posSemidef.",
                DescribeRole.Theorem),
            Entry("history-free-span-positive", "extensionLaw_kernel_posSemidef",
                "The formal finitely supported span has a positive form",
                Frame(Imp(Law, PSD(K))),
                "Matrix.PosSemidef on the arbitrary label type means Hermitian symmetry and nonnegativity of the double kernel sum for every finitely supported complex coefficient family. The proof obtains symmetry from a two-label list and reduces each coefficient sum to its actual finite support. This supplies the positive-form input of C129 Theorem 2.4, without assuming a historical Hilbert space.",
                DescribeRole.Theorem),
            Paragraph(Text(
                "This module proves the forward implication of C129 Theorem 2.3. The converse construction for singular blocks, the certified-chain coverage criterion, and the label-preserving minimal Hilbert representation of Theorem 2.4 remain open here. No CP, Born or physical-control conclusion is inferred.")))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string narrative, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))), role);

    private static Formula ExtensionFormula()
    {
        Formula g = F.Id("G"), c = F.Id("c"), r = F.Id("r");
        Formula u = Call("Unit");
        Formula block = Call("fromBlocks", g, Mul(g, c), Mul(Star(c), g),
            Seq(Mul(Mul(Star(c), g), c), Sp, Plus, Sp,
                Call("constantMatrix", Mul(Star(r), r))));
        Formula body = All(g, Matrix(I, I), All(c, Matrix(I, u), All(r, C,
            Eq(Call("residualExtension", g, c, r), block))));
        return All(I, Type, Seq(OpenBracket, Call("Fintype", I), CloseBracket,
            Comma, Sp, body));
    }

    private static Formula LawFormula()
    {
        Formula n = F.Id("n"), h = F.Id("h"), c = F.Id("c"), r = F.Id("r");
        return All(n, N, All(L, Arrow(Fin(n), X), All(h, X,
            Ex(c, Matrix(Fin(n), Call("Unit")), Ex(r, C,
                Eq(Call("finiteGram", K, Call("append", L, h)),
                    Call("residualExtension", Gram, c, r)))))));
    }
}
