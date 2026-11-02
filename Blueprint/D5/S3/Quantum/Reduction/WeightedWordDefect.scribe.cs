using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class WeightedWordDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete weighted pair defect controls every finite Hermitian operator word.",
        H("Weighted defects of finite operator words"),
        Blocks(
            Paragraph(Text("Let Phi be any unital completely positive linear map from complex d by d matrices to complex k by k matrices. No trace preservation, idempotence, or dynamical assumption is imposed on Phi. Every matrix norm in this result is the operator norm on the Euclidean coordinate Hilbert space. The finite list is ordered and may contain repetitions or zero matrices; its length is unrestricted, including zero and one.")),
            Describe.Lean(
                DescribeId.Create("ucp-word-pair-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/WeightedWordDefect.ucp_word_pair_bound"),
                H("The weighted pair bound"),
                StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the jth letter set M_j equal to its Euclidean operator norm and epsilon_j equal to the square root of the operator norm of Phi(A_j adjoint times A_j) minus Phi(A_j) adjoint times Phi(A_j). The norm of Phi applied to the ordered product minus the ordered product of the images is at most the sum over all positional pairs i less than j of epsilon_i times epsilon_j times the product of M_r over all remaining positions. The function pairSum is exactly this finite sum: the two omitted factors are replaced by one. No norm is divided out.")),
                    Paragraph(Text("FiniteKrausChannel.krausRepresentation supplies the original rectangular matrices L_r with Phi(X) equal to the sum of L_r X L_r adjoint. The source convention K_r is L_r adjoint. Stack these adjoints into V and amplify X by the identity on the finite Kraus index. Unitality proves V adjoint times V equals the identity, and compressing this amplification gives the original Phi on every matrix. The original IsometricCompression support, compress, and normal definitions implement this same frame. With Q equal to I minus V V adjoint, the discarded map D(X) is Q pi(X) V. Its Gram product is exactly the original multiplicative defect. The C-star norm identity proves that the norm of D(X) equals the square root used in the bound.")),
                    Paragraph(Text("The intertwining residual for the entire ordered word is bounded by the sum of the single-deletion weights. Projecting the residual bounds the leakage of the word. The first Hermitian letter then contributes its leakage norm times the remaining single-deletion sum; induction supplies the remaining pairs with the first letter's norm as a factor. This analytic induction works at every finite length. Recursive weights are equated to the explicit sums on finite positions.")),
                    Paragraph(Text("If all letters are chosen from two Hermitian contractions and both squared defects have norm at most delta, every pair contributes at most delta. There are length choose two pairs, so the word error is at most that number times delta. This consequence concerns finite words; it asserts neither uniform control over all word lengths nor convergence of an infinite iteration."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula x, Formula i) => Seq(x, Underscore, Grp(i));
    private static Formula At(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Adj(Formula x) => Seq(x, Caret, Grp(Star));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert, Underscore, Grp(F.Id("op")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula BoundFormula()
    {
        Formula d = F.Id("d"), k = F.Id("k"), l = F.Id("l"), f = F.Id("f");
        Formula i = F.Id("i"), j = F.Id("j"), r = F.Id("r"), a = F.Id("A");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", d, d, complex);
        Formula fin = Call("Fin", l);
        Formula ai = Sub(a, i), aj = Sub(a, j), ar = Sub(a, r);
        Formula Error(Formula x) => Seq(Sqrt, Grp(Norm(Seq(
            At(f, Seq(Adj(x), x)), Minus, Adj(At(f, x)), At(f, x)))));
        Formula orderedProduct = Seq(Prod, Underscore, Grp(D(0), Le, Sp, r, Lt, l));
        Formula conclusion = Seq(
            Norm(Seq(At(f, Seq(orderedProduct, ar)), Minus, orderedProduct, At(f, ar))),
            Sp, Le, Sp, Sum, Underscore, Grp(D(0), Le, Sp, i, Lt, j, Lt, l),
            Error(ai), Error(aj), Sp, Prod, Underscore,
            Grp(D(0), Le, Sp, r, Lt, l, Comma, r, Neq, Sp, i, Comma, r, Neq, Sp, j), Norm(ar));
        Formula body = Seq(
            Open, Forall, Sp, i, InMacro, Sp, fin, Comma, Sp, Adj(ai), Eq, ai, Close,
            Sp, Implies, Sp, conclusion);
        return Disp(All("d", F.Id("Type"), All("k", F.Id("Type"), Seq(
            Inst("Fintype", d), Inst("DecidableEq", d),
            Inst("Fintype", k), Inst("DecidableEq", k),
            All("l", Seq(Mathbb, Grp(F.Id("N"))),
                All("f", Call("UCP", matrix, Call("Matrix", k, k, complex)),
                    All("A", new Formula.TypeArrow(fin, matrix), body)))))));
    }
}
