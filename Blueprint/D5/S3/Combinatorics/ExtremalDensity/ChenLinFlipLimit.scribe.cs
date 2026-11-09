using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ExtremalDensity;

internal sealed class ChenLinFlipLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite tournament path defects and convergence",
        H("Finite tournament path defects and convergence"), Blocks(
            Paragraph(Text(
                "An orientation is a list of signs, with true denoting a forward arc and false a "
                + "backward arc. Its flips count adjacent unequal signs. ArcPreserving quantifies "
                + "over every map from Fin(length+1) to Fin(N); maps need not be injective. "
                + "The density homDensity is homCount divided by N^(length+1). TAS quantifies over "
                + "every positive N and every loopless tournament relation on Fin(N), with bound "
                + "(1/2)^length. Enumeration of the vertices identifies these hosts with arbitrary "
                + "finite nonempty loopless tournaments. The function f is the maximum of precisely "
                + "those m in {0,...,k} for which every length-k orientation with fewer than m flips "
                + "is TAS. The set contains zero. No property at length zero is used. "
                + "The motivating question is Question 6.1 in Hao Chen and Yupeng Lin, "
                + "Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko, "
                + "https://arxiv.org/abs/2609.14655v1.")),
            Node("full-convergence", "FullConvergence", "Convergence over all positive lengths",
                Iff(V("FullConvergence"), Some("L", Real,
                    All("e", Real, Imp(Lt(N(0), V("e")), Some("K", Nat,
                        And(Le(N(1), V("K")), All("k", Nat, Imp(Le(V("K"), V("k")),
                            Lt(Call("abs", Sub(Div(Call("f", V("k")), V("k")), V("L"))),
                                V("e")))))))))),
                "This is the epsilon/K assertion for the source's exact strict threshold. "
                + "The positive-length quantifiers retain saturation at f(k)=k.", DescribeRole.Definition),
            Node("threshold-bounded", "f_le", "The saturated threshold is bounded",
                All("k", Nat, Le(Call("f", V("k")), V("k"))),
                "Every member of thresholds(k) belongs to {0,...,k}.", DescribeRole.Theorem),
            Node("least-defect", "exists_bad_at_f", "A nonsaturated threshold is attained by a defect",
                All("k", Nat, Imp(Lt(Call("f", V("k")), V("k")),
                    Some("w", Words, And(Eq(Call("length", V("w")), V("k")),
                        And(Eq(Call("flips", V("w")), Call("f", V("k"))),
                            Not(Call("TAS", V("w")))))))),
                "The property holds below f(k). Its failure at f(k)+1 supplies an orientation "
                + "with exactly f(k) flips, rather than merely an orientation below a different threshold.",
                DescribeRole.Theorem),
            Node("reflected-transfer", "reflected_pair_transfer", "Reflection produces a Gram transfer",
                MatrixFamily(All("A", Mat, All("w", Words,
                    Eq(Call("transfer", V("A"), Call("append", V("w"), Call("reflect", V("w")))),
                        Mul(Call("transfer", V("A"), V("w")),
                            Call("transpose", Call("transfer", V("A"), V("w")))))))),
                "Reflection reverses the word and complements every sign. It therefore transposes "
                + "the product, retaining its endpoints and their correlations.", DescribeRole.Theorem),
            Node("reflection-mass", "reflected_mass_sq_le", "Reflection amplifies the average",
                MatrixFamily(Seq(Instance("Nonempty", V("V")), All("B", Mat,
                    Le(Pow(Call("mass", V("B")), N(2)),
                        Call("mass", Mul(V("B"), Call("transpose", V("B")))))))),
                "Mass is the sum of all entries divided by the number of indices. The mass of "
                + "B times its transpose is the mean of the squares of the column sums. "
                + "Cauchy-Schwarz bounds it below by the square of the original mass. "
                + "No independent gluing of endpoint densities is used.", DescribeRole.Theorem),
            Node("tournament-padding", "tournament_padding", "Every bounded remainder admits padding",
                MatrixFamily(Seq(Instance("Nonempty", V("V")), All("R", Relation,
                    Imp(Call("IsTournament", V("R")), All("w", Words, All("s", Nat,
                        Some("v", Words, And(Eq(Call("length", V("v")), V("s")),
                            Le(Mul(Pow(PaddingFactor, V("s")), TransferMass(V("w"))),
                                TransferMass(Call("append", V("w"), V("v")))))))))))),
                "Put A(i,j)=2/N when i points to j and zero otherwise. Looplessness and the unique "
                + "orientation of distinct pairs give sum_j(A(i,j)+A(j,i))=2(N-1)/N. Thus the masses "
                + "of the two possible one-edge extensions sum to 2(N-1)/N times the previous mass. "
                + "At least one sign retains a factor (N-1)/N. Induction selects an s-edge tail "
                + "retaining its s-th power, inside the same original tournament. It does not assert "
                + "that an arbitrary prescribed tail is safe.", DescribeRole.Theorem),
            Node("moment-growth", "moment_geometric_lower", "All repetition counts amplify",
                MatrixFamily(All("C", Mat, Imp(Call("PosSemidef", V("C")),
                    All("x", Arrow(V("V"), Real), Imp(Lt(N(0), Call("dot", V("x"), V("x"))),
                        Imp(Lt(N(0), Call("moment", V("C"), V("x"), N(1))), All("n", Nat,
                            Le(Pow(Call("moment", V("C"), V("x"), N(1)), V("n")),
                                Call("moment", V("C"), V("x"), V("n")))))))))),
                "Moment(C,x,n) is x dot C^n x divided by x dot x. Cauchy-Schwarz in the "
                + "positive semidefinite form C^n gives a(n+1)^2 <= a(n)a(n+2). With a(0)=1 and "
                + "a(1)>0, successive moment ratios are nondecreasing, so a(n)>=a(1)^n. "
                + "This bound holds for every natural repetition count, not only a subsequence.",
                DescribeRole.Theorem),
            Node("reflected-powers", "reflected_power_amplification", "Exponential reflected amplification",
                MatrixFamily(Seq(Instance("Nonempty", V("V")), All("B", Mat,
                    Imp(Lt(N(1), Call("mass", V("B"))), All("m", Nat,
                        Le(Pow(Call("mass", V("B")), Mul(N(2), V("m"))),
                            Call("mass", Pow(Mul(V("B"), Call("transpose", V("B"))), V("m"))))))))),
                "The all-ones moment is the mass of the matrix power. The Gram matrix is positive "
                + "semidefinite, its first mass is at least mass(B)^2, and the geometric moment "
                + "bound gives mass((B B^T)^m)>=mass(B)^(2m) for every m.", DescribeRole.Theorem),
            Paragraph(Text(
                "For the convergence argument, call (k,r) a defect when a length-k orientation "
                + "with r flips has normalized density q=2^k t(P,T)>1 in some finite host T. "
                + "For a positive-length defect N>=2. The transfer B for P has mass q. The reflected "
                + "word W=P reflect(P) has transfer C=B B^T, length 2k, and 2r+1 flips. With x "
                + "the all-ones vector, moment(C,x,m)=mass(C^m). The reflection and moment bounds "
                + "give mass(C^m)>=q^(2m).")),
            Paragraph(Text(
                "For every n write n=2km+s with 0<=s<2k. The word W repeated m times has "
                + "2m(r+1)-1 flips when m>=1. Append the tail selected by the padding inequality. "
                + "Its normalized density is at least c^s q^(2m), where c=(N-1)/N lies in (0,1). "
                + "This is at least c^(2k-1) q^(2m), which exceeds one for all sufficiently large m. "
                + "The resulting length-n path is therefore a defect for every sufficiently large n. "
                + "Its flips are at most 2m(r+1)-1+s, hence at most ((r+1)/k)n+2k. This proves "
                + "eventual upper propagation f(n)/n < (r+1)/k+delta for every positive delta.")),
            Paragraph(Text(
                "Let L be the infimum of {1} together with all (r+1)/k from defects. This nonempty "
                + "set is bounded below by zero. At a saturated length f(n)=n, one has f(n)/n>=L. "
                + "At a nonsaturated length the least-defect fact gives a defect with r=f(n), so "
                + "L<=(f(n)+1)/n. Thus f(n)/n>=L-1/n at every positive length. For the upper bound, "
                + "choose an element of the defining set below L+epsilon/2. If it is 1, saturation "
                + "bounds every f(n)/n by 1. Otherwise it is a defect ratio, and upper propagation "
                + "with delta=epsilon/2 applies to every sufficiently large length. Combining this "
                + "with 1/n<epsilon proves convergence to L over all positive lengths. The argument "
                + "does not determine a numerical value of L.")))));

    private static DocumentBlock.Describe Node(string id, string name, string title, Formula formula,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);

    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula N(int n) => new Formula.Number(n);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Words => Call("List", V("Bool"));
    private static Formula Mat => Call("Matrix", V("V"), V("V"), Real);
    private static Formula Relation => Arrow(V("V"), Arrow(V("V"), V("Prop")));
    private static Formula PaddingFactor => Div(Sub(Call("card", V("V")), N(1)), Call("card", V("V")));
    private static Formula TransferMass(Formula word) => Call("mass", Call("transfer",
        Call("normalizedArcMatrix", V("R")), word));
    private static Formula MatrixFamily(Formula body) => All("V", V("Type"),
        Seq(Instance("Fintype", V("V")), Instance("DecidableEq", V("V")), body));
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, a);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
