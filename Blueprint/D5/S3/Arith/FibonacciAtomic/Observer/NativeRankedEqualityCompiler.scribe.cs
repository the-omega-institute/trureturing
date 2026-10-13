using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeRankedEqualityCompilerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeRankedEqualityCompiler", H("Exact scalar formulas for native tree equality"), Blocks(
            Describe.Lean(DescribeId.Create("native-ranked-equality-compilation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler.ranked_equality_compilation"),
                H("Native equality is a finite conjunction of offset equalities"), EqualityStatement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The native source is the ordered free binary magma on alpha and beta. Substitution sends alpha to beta and beta to the pair of beta and alpha. Its r-th iterate at alpha is the rank-r atom. A RankedExpr has finite native grounds, fixed powers of residual or scalar names, and ordered pairs. Each original scalar name denotes one shared natural rank, and each residual name denotes one shared finite native tree.")),
                    Paragraph(Text("Fix a finite residual tuple z before choosing the scalar tuple n. An offset is either a constant c or n(j)+c. Normalize each finite ground into constant-rank leaves 0 and 1; normalize a decorated scalar into its original variable plus the decoration. A decorated residual becomes the expanded finite tree obtained by applying its fixed substitution power to z(i). Explicit pairs remain ordered pairs. The interpretation of this finite rank term is exactly rankedEval at the same n and z.")),
                    Paragraph(Text("For a rank term T, its symbolic right clock K is its leaf offset when T is a leaf, and K(B)+2 when T is the pair of A and B. Its atomicity conditions C are empty at a leaf. At a pair they are C(A), C(B), and K(A)=K(B)+1. Structural induction proves that T evaluates to the rank-r atom exactly when every condition in C(T) holds and K(T)=r. Ranks zero and one are separated from pairs by the native constructors. At every higher rank the native Fibonacci recurrence identifies the two children.")),
                    Paragraph(Text("Compare two leaves by equating their offsets. Compare a leaf with a pair by imposing the pair's atomicity conditions and equating its clock with the leaf offset. Compare two pairs by conjoining the comparisons of corresponding children. Thus a rank leaf may equal a compound native tree; treating them as disjoint syntax would give an incorrect compiler. The resulting finite equation list is interpreted by one common scalar tuple throughout.")),
                    Paragraph(Text("conditionsFormula translates constant and variable offsets into the natural-number Presburger language with zero, one and addition, then conjoins the equality atoms. equalityFormula is quantifier free and uses only the original scalar names as free variables; unused names need not occur. Its realization is equivalent to native equality for every scalar tuple, including ranks zero and one, repeated variables, zero dimensions and closed ground expressions. No upper rank bound or rank enumeration is used. The theorem concerns finite syntax translation; it does not assert a bound on expanded ground size or the cost of unary numeral syntax."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-rank-support-compilation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler.support_compilation"),
                H("One formula describes the entire feasible-rank support"), SupportStatement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Negatives(pairs,n,z) abbreviates the conjunction of all listed disequalities at the common n and z. For a finite list of pairs of ranked expressions, use the existing uniformSeparator for that entire list. Negate each equality formula after substituting this one residual tuple, then conjoin all negatives. The resulting supportFormula is quantifier free. It holds at n exactly when there is one finite residual tuple satisfying every listed disequality at that same n.")),
                    Paragraph(Text("The uniform residual reflection theorem makes this a joint statement. If one tuple satisfies every negative, no listed equality is universal in the residuals, and every negative therefore holds at the common separator. Conversely the separator itself is a finite satisfying tuple. There is no separate choice of residual tuple or scalar ranks for individual conjuncts. The empty list gives true support, and either dimension may be zero.")),
                    Paragraph(Text("A Presburger policy supplied with its own formula and semantic correspondence can be conjoined with this support formula. An arbitrary Prop-valued policy does not automatically have such a representation or an executable decision procedure. Fixed finite coordinates must be substituted before computing the separator for the remaining expressions. Unknown finiteness of completion trees, serialized observation decoding, and general quantified arithmetic decisions are separate questions. The formula translation uses the native Fibonacci recurrence and the existing uniform residual theorem; it makes no claim of literature originality."))
                ), DescribeRole.Theorem)
        )));
    private static StatementSource EqualityStatement()
    {
        var ranks = Arr(Call("Fin", V("k")), V("Nat"));
        var expr = Call("RankedExpr", V("k"), V("m"));
        var formula = Call("equalityFormula", V("z"), V("E"), V("F"));
        return StatementSource.FromAuthor(Disp(All("k,m", V("Nat"),
            All("z", Arr(Call("Fin", V("m")), V("Source")),
                All("E,F", expr, AndOf(Call("IsQF", formula),
                    All("n", ranks, IffOf(Call("Realize", formula, V("n")),
                        EqOf(Call("rankedEval", V("n"), V("z"), V("E")),
                            Call("rankedEval", V("n"), V("z"), V("F")))))))))));
    }
    private static StatementSource SupportStatement()
    {
        var expr = Call("RankedExpr", V("k"), V("m"));
        var formula = Call("supportFormula", V("pairs"));
        return StatementSource.FromAuthor(Disp(All("k,m", V("Nat"),
            All("pairs", Call("List", Call("Prod", expr, expr)),
                AndOf(Call("IsQF", formula), All("n", Arr(Call("Fin", V("k")), V("Nat")),
                    IffOf(Call("Realize", formula, V("n")),
                        Some("z", Arr(Call("Fin", V("m")), V("Source")),
                            Call("Negatives", V("pairs"), V("n"), V("z"))))))))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula AndOf(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
}
