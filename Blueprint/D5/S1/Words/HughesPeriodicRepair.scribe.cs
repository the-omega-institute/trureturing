using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class HughesPeriodicRepairDocument : IScribeDocumentDefinition
{
    private static readonly Formula A = F.Id("A"), B = F.Id("B");
    private static readonly Formula Hn = F.Id("H"), J = F.Id("J");
    private static readonly Formula K = F.Id("K"), L = F.Id("L");
    private static Formula Letters(params Formula[] xs) => Call("List", xs);
    private static Formula T => Letters(A, B, A);
    private static Formula Pow(Formula n) => Call("wordPower", n, T);
    private static Formula Join(params Formula[] xs) => Call("concat", xs);
    private static Formula U => Join(Pow(Hn), Letters(A, B, A, B, A), Pow(J));
    private static Formula V => Pow(Add(Add(K, Num(1)), Add(L, Num(1))));
    private static Formula Z => Join(Pow(K), Letters(A, B), Pow(Add(Hn, Num(1))),
        Letters(A), Pow(Add(L, Num(1))), Letters(B, A), Pow(J));
    private static Formula Left => Join(Pow(Hn), Letters(A, B));
    private static Formula Right => Join(Letters(B, A), Pow(J));
    private static Formula P => Pow(Add(K, Num(1)));
    private static Formula Q => Pow(Add(L, Num(1)));
    private static Formula X => Join(Pow(K), Letters(A, B));
    private static Formula W => Join(Left, P, Letters(A), Q, Right);
    private static Formula M => Call("fiveMask", Left, P, Letters(A), Q, Right);
    private static Formula N => Call("fiveMask", Left, X, Letters(A), Join(Letters(A), Q), Right);
    private static Formula Cut(Formula i) => Call("fourCuts", Left, P, Letters(A), Q, Right, i);
    private static Formula E => Call("fourCuts", Left, X, Letters(A), Join(Letters(A), Q), Right, Num(0));
    private static Formula RepairStatement()
    {
        Formula U = F.Id("u"), V = F.Id("v"), W = F.Id("w");
        Formula M = F.Id("M"), N = F.Id("N"), E = F.Id("E"), Z = F.Id("Z");
        Formula Cut(Formula n) => Call("C", n);
        Formula i = F.Id("i");
        Formula exchange = All("i", Call("Fin", Num(4)), Conjoin(
            Equal(Call("original", Cut(i)), W), Call("Admissible", Cut(i), M),
            Equal(Call("successor", Cut(i)), Call("ite",
                new Formula.Relation(i, FormulaRelationOperator.LessThan, Num(2)),
                Join(V, U), Join(U, V))),
            Equal(Call("degree", U, V, Call("successor", Cut(i))), Num(1))));
        Formula body = Conjoin(Call("ValidMask", U, V, W, M), Equal(Call("rho", M), Num(3)),
            exchange, Call("ValidMask", U, V, W, N), Equal(Call("rho", N), Num(3)),
            Equal(Call("original", E), W), Call("Admissible", E, N),
            Equal(Call("successor", E), Z), Equal(Call("degree", U, V, Call("successor", E)), Num(2)),
            Implies(Equal(Call("degree", U, V, W), Num(3)),
                Conjoin(Call("IsMinimumMask", U, V, W, M, Num(3)),
                    Call("IsMinimumMask", U, V, W, N, Num(3)))));
        return All("alpha", Call("Type"), All("A", F.Id("alpha"), All("B", F.Id("alpha"),
            Implies(NotEqual(A, B), All("H", Call("Nat"), All("J", Call("Nat"),
                All("K", Call("Nat"), All("L", Call("Nat"), body))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native periodic masks, their exchanges, and a contiguous-deletion obstruction.",
        H("Periodic Masks and an Exact Shifted Successor"), Blocks(
            Paragraph(Text("Let A and B be distinct letters of an arbitrary alphabet and let "
                + "T=ABA. The four natural numbers H,J,K,L represent the positive parameters "
                + "h=H+1,j=J+1,k=K+1,l=L+1. Thus zero exterior powers and every boundary "
                + "case with a positive parameter equal to one are included.")),
            Describe.Lean(DescribeId.Create("shifted-successor-degree"),
                DeclarationHandle.Create("D5/S1/Words/HughesPeriodicRepair.shifted_successor_degree"),
                H("The exact successor degree"), StatementSource.FromAuthor(
                    All("alpha", Call("Type"), All("A", F.Id("alpha"),
                        All("B", F.Id("alpha"), All("H", Call("Nat"),
                            All("J", Call("Nat"), All("K", Call("Nat"),
                                All("L", Call("Nat"), Implies(NotEqual(A, B),
                                    Equal(Call("degree", U, V, Z), Num(2))))))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The ordered inserted source is T^H ABABA T^J and the "
                        + "base source is T^(K+L+2). The output is "
                        + "T^K AB T^(H+1) A T^(L+1) BA T^J. Its actual mask with blocks "
                        + "V^(3K+2), U^(3H+3), V^(3L+4), U^(3J+2) has two inserted runs.")),
                    Paragraph(Text("A nonempty inserted source has degree one exactly when "
                        + "it can be deleted as one contiguous block, leaving the base source. "
                        + "Every cut of a power of ABA lies at a period boundary, after A, "
                        + "or after AB. Remove all entries equal to two from the actual "
                        + "A-gap sequence. Inserting the whole source at those cuts gives "
                        + "[1,1,1], [1,3,1,1,1], or [1,1,1,3,1], with the outer cut cases "
                        + "again giving [1,1,1]. The displayed output instead gives "
                        + "[1,1,3,1,1]. Hence no such deletion is possible. Every valid "
                        + "mask has at least two runs, and the explicit two-run mask attains "
                        + "this lower bound.")),
                    Paragraph(Text("This statement computes the native degree of the "
                        + "displayed successor. It does not assert that the preceding output "
                        + "has degree three or classify its minimum masks."))), DescribeRole.Theorem),
            Paragraph(Text("For each choice of A,B,H,J,K,L in the next theorem, use the "
                + "following word, mask, and cut abbreviations:")),
            Paragraph(Math(Equal(F.Id("u"), U))),
            Paragraph(Math(Equal(F.Id("v"), V))),
            Paragraph(Math(Equal(F.Id("w"), W))),
            Paragraph(Math(Equal(F.Id("M"), M))),
            Paragraph(Math(Equal(F.Id("N"), N))),
            Paragraph(Math(Equal(F.Id("E"), E))),
            Paragraph(Math(Equal(F.Id("Z"), Z))),
            Paragraph(Math(All("i", Call("Fin", Num(4)),
                Equal(Call("C", F.Id("i")), Cut(F.Id("i")))))),
            Describe.Lean(DescribeId.Create("periodic-repair"),
                DeclarationHandle.Create("D5/S1/Words/HughesPeriodicRepair.periodic_repair"),
                H("The original and shifted native masks"),
                StatementSource.FromAuthor(RepairStatement()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Put a=T^H AB, c=BA T^J, p=T^(K+1), q=T^(L+1), "
                        + "and x=T^K AB. The definitions fiveMask and fourCuts use actual "
                        + "letter lengths and literal contiguous cuts. Thus M has label blocks "
                        + "U^|a| V^|p| U V^|q| U^|c|, while N has blocks "
                        + "U^|a| V^|x| U V^(1+|q|) U^|c|. Both project to the same "
                        + "ordered sources u=aAc and v=pq in w=apAqc, and both have three U-runs.")),
                    Paragraph(Text("The four cuts of M, indexed 0,1,2,3, are respectively "
                        + "(empty,a,p,Aqc), (a,p,A,qc), (ap,A,q,c), (apA,q,c,empty). "
                        + "All exchanged blocks are nonempty and satisfy the native maximal "
                        + "endpoint conditions. Their successor words are vu,vu,uv,uv and "
                        + "have native degree one. The first cut E of N is "
                        + "(empty,a,x,AAqc); it is admissible and its successor is the word "
                        + "Z above. The contiguous-deletion obstruction proves degree two.")),
                    Paragraph(Text("If the original degree is three, M and N are both "
                        + "minimum masks; E therefore decreases the degree by exactly one. "
                        + "The theorem retains this hypothesis. It supplies neither a full "
                        + "classification of masks nor a proof that the original degree is "
                        + "three for all parameters. The twelve-mask subfamily, its first "
                        + "mask, arbitrary A-free block coding, and the common primitive-period "
                        + "argument with exterior contexts are outside these statements."))), DescribeRole.Theorem))));

    private static Formula All(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Conjoin(params Formula[] xs)
    {
        Formula result = xs[^1];
        for (int i = xs.Length - 2; i >= 0; --i)
            result = new Formula.Logic(xs[i], FormulaLogicOperator.And, result);
        return result;
    }
}
