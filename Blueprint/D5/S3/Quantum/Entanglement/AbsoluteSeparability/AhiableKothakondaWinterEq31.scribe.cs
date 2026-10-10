using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class AhiableKothakondaWinterEq31Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/ahiablekothakondawinter2026geometry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The linear spectral condition in Eq. (31) implies absolute separability.",
        H("Ahiable--Kothakonda--Winter Eq. (31) and absolute separability"),
        Blocks(
            Describe.Lean(DescribeId.Create("akw-eq31-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The spectral condition"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Theorem 6.2, Eq. (31), assumes a decreasingly ordered spectrum λ₁ ≥ ⋯ ≥ λ_mn ≥ 0 and requires 2λ_mn + Σ_{k=1}^{m−1} λ_{mn−k} ≥ Σ_{k=1}^{m−1} λ_k. Section 7 asks whether this condition implies absolute separability. The definition in Section 1 requires every global unitary conjugate UρU† to remain separable. The statement quantifies all 2 ≤ m ≤ n, every positive semidefinite trace-one state, and every global unitary, using separableCone, the cone of finite sums of Kronecker products of positive semidefinite factors. In the displayed formula lambda(i) is the decreasing eigenvalues₀ of rho at zero-based index i; lambda(0) ≥ ⋯ ≥ lambda(mn−1) ≥ 0.")))),
            Describe.Lean(DescribeId.Create("akw-eq31-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Absolute separability follows"),
                StatementSource.FromAuthor(F.Id("claim")), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The spectral theorem orders an eigenbasis and telescopes the spectrum into the identity, the codimension-one projection ray, and the rays a_k I + 2P_k with a_k = min(k,m−1,mn−k−1). The three existing ray constructions prove separability of each summand; Eq. (31) makes the identity coefficient nonnegative. Finite sums and nonnegative scalings preserve separability."))),
                DescribeRole.Theorem))));

    private static Formula ClaimFormula()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var rho = F.Id("rho");
        var U = F.Id("U");
        var C = F.Seq(Mathbb, Grp(F.Id("C")));
        var N = F.Seq(Mathbb, Grp(F.Id("N")));
        var pair = F.Seq(Call("Fin", m), Times, Sp, Call("Fin", n));
        var matrix = Call("Matrix", pair, pair, C);
        var density = And(Call("PosSemidef", rho), Eq(Call("trace", rho), D(1)));
        var dim = Mul(m, n);
        var k = F.Id("k");
        var condition = Le(
            Sum("k", Call("Fin", Sub(m, D(1))), Call("lambda", k)),
            Add(Mul(D(2), Call("lambda", Sub(dim, D(1)))),
                Sum("k", Call("Fin", Sub(m, D(1))),
                    Call("lambda", Sub(Sub(dim, k), D(2))))));
        var conclusion = All("U", matrix,
            Imp(Seq(U, InMacro, Sp, Call("unitaryGroup", pair, C)),
                Call("separableCone", Mul(Mul(U, rho), Call("star", U)))));
        var body = All("rho", matrix, Imp(density, Imp(condition, conclusion)));
        return All("m", N, All("n", N, Imp(And(Le(D(2), m), Le(m, n)), body)));
    }

    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(F.Id(name), [.. xs]);
    private static Formula Eq(Formula a, Formula b) => F.Seq(a, F.Eq, b);
    private static Formula Le(Formula a, Formula b) => F.Seq(a, Leq, Sp, b);
    private static Formula And(Formula a, Formula b) => F.Seq(Par(a), Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => F.Seq(Par(a), Rightarrow, Sp, b);
    private static Formula Add(Formula a, Formula b) => F.Seq(a, Plus, b);
    private static Formula Sub(Formula a, Formula b) => F.Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => F.Seq(a, Cdot, Sp, b);
    private static Formula Sum(string name, Formula type, Formula body) =>
        F.Seq(new Formula.Subscript(F.Sum, F.Seq(F.Id(name), Colon, type)), Sp, body);
    private static Formula Par(Formula f) => F.Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        F.Seq(F.Forall, Sp, Par(F.Seq(F.Id(name), Colon, type)), Comma, Sp, body);
}
