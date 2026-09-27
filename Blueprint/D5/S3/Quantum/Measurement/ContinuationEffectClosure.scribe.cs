using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ContinuationEffectClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/ContinuationEffectClosure.";

    private static readonly Formula J = F.Id("j"), K = F.Id("k"), Hx = F.Id("H"), W = F.Id("W"), N = F.Id("n");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Starting from an r-dimensional real space of Hermitian d by d matrices, the spaces closed step by step "
            + "under the duals of an arbitrary family of branches, each with a finite Kraus family, stop growing "
            + "after d^2 - r steps, at the least "
            + "space that contains the start and is invariant under every branch dual.",
        H("Finite Closure of Continuation Effect Spaces"),
        Blocks(
            Node("dual", "Branch duals",
                Disp(Seq(Dual(Hx), Sp, Eq, Sp, Sum, Underscore, Grp(K), Sp, Sub("K", Seq(J, Sp, K)), Caret, Grp(Star),
                    Sp, Hx, Sp, Sub("K", Seq(J, Sp, K)))),
                "The branch j acts by the finite Kraus family K_{jk}; its dual acts on effects as above and is "
                    + "real linear.",
                "branchDual", DescribeRole.Definition),
            Node("space", "Continuation effect spaces",
                Disp(Seq(Sub("Z", Seq(N, Plus, D(1))), Sp, Eq, Sp, Operatorname, Grp(F.Id("span")), Underscore,
                    Grp(Mathbb, Grp(F.Id("R"))), Open, Sub("Z", N), Sp, Cup, Sp,
                    PhiSub(J), Caret, Grp(Star), Open, Sub("Z", N), Close, Sp, F.Text,
                    Grp(Sp, F.Id("for"), Sp, F.Id("all"), Sp), J, Close)),
                "Each step adds the images of the current space under every branch dual.",
                "continuationSpace", DescribeRole.Definition),
            Node("closure", "Finite closure and minimality", TheoremFormula(),
                "Let Z_0 be a real space of Hermitian d by d matrices of dimension r. If Z_{k+1} = Z_k, then Z_k is "
                    + "invariant under every branch dual and all later spaces equal it. Branch duals preserve "
                    + "Hermiticity, so every Z_k lies in the real space of Hermitian d by d matrices, which has "
                    + "dimension d^2; hence every Z_k has real dimension at most d^2. If the chain still grew at "
                    + "step d^2 - r, all earlier steps would be strict and the dimension would exceed d^2. Finally, "
                    + "every invariant space W containing Z_0 contains each Z_k by induction.",
                "continuationSpace_closure", DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stop = Seq(F.Id("d"), Caret, Grp(D(2)), Minus, F.Id("r"));
        Formula zs = Sub("Z", stop);
        return Disp(Seq(
            Sub("Z", D(0)), Sp, Subseteq, Sp, Operatorname, Grp(F.Id("Herm")), Open, F.Id("d"), Close, Comma, Sp,
            Operatorname, Grp(F.Id("dim")), Sp, Sub("Z", D(0)), Sp, Eq, Sp, F.Id("r"), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, N, Sp, Geq, Sp, stop, Comma, Sp, Sub("Z", N), Sp, Eq, Sp, zs, Comma, Quad, Sp,
            Sub("Z", D(0)), Sp, Subseteq, Sp, zs, Comma, Quad, Sp,
            Forall, Sp, J, Comma, Sp, PhiSub(J), Caret, Grp(Star), Open, zs, Close, Sp, Subseteq, Sp, zs, Comma,
            RowBreak, Grp(),
            Forall, Sp, W, Comma, Sp, Sub("Z", D(0)), Sp, Subseteq, Sp, W, Sp, Land, Sp,
            Open, Forall, Sp, J, Comma, Sp, PhiSub(J), Caret, Grp(Star), Open, W, Close, Sp, Subseteq, Sp, W,
            Close, Sp, Rightarrow, Sp, zs, Sp, Subseteq, Sp, W, Dot));
    }

    private static Formula Dual(Formula argument) =>
        Seq(PhiSub(F.Id("j")), Caret, Grp(Star), Open, argument, Close);

    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));

    private static Formula PhiSub(Formula index) => Seq(Phi, Underscore, Grp(index));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("continuation-closure-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
