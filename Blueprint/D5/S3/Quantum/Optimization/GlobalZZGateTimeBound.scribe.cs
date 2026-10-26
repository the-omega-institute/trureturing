using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Optimization;

internal sealed class GlobalZZGateTimeBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Optimization/GlobalZZGateTimeBound";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/QuantumContext/basslerheinrichkliesch2024gzz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every real symmetric zero-diagonal coupling matrix admits a nonnegative sign schedule within the parity-dependent gate-time bound.",
        H("The global ZZ gate-time upper bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sign-vec"),
                DeclarationHandle.Create(Module + ".SignVec"),
                H("Sign vectors with a fixed final sign"),
                StatementSource.FromAuthor(Disp(SignVecFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A sign vector is a Boolean function on Fin n whose final coordinate is false. "
                    + "The Boolean b represents the real sign (-1) to the power Bool.toNat(b), so false represents plus one. "
                    + "The condition Fin.val(i) + 1 = n identifies the final coordinate without requiring n to be positive. "
                    + "This encodes the source's convention that the final sign is plus one "
                    + "(J_shaping.tex, lines 355-362); at n = 0 the condition is vacuous."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-feasible"),
                DeclarationHandle.Create(Module + ".IsFeasible"),
                H("A nonnegative sign schedule"),
                StatementSource.FromAuthor(Disp(IsFeasibleFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The real weights lam are nonnegative, and their weighted sign products reproduce every strictly upper triangular entry of M. "
                    + "Subtype.val explicitly extracts the Boolean function from each sign vector. "
                    + "This is feasibility for the source's linear program (J_shaping.tex, lines 265-288). "
                    + "The predicate itself imposes no condition on the diagonal or lower triangular entries of M."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("off-diag-sup"),
                DeclarationHandle.Create(Module + ".offDiagSup"),
                H("The largest absolute upper triangular entry"),
                StatementSource.FromAuthor(Disp(OffDiagSupFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Take the finite maximum over optional ordered pairs of indices. None contributes zero; "
                    + "a pair contributes the absolute entry when its first index is smaller, and zero otherwise. "
                    + "The extra zero makes this maximum defined and nonnegative even when there is no such pair. "
                    + "For a symmetric matrix this is the source's infinity norm of the vectorized off-diagonal entries "
                    + "(J_shaping.tex, lines 278 and 448)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gate-bound"),
                DeclarationHandle.Create(Module + ".gateBound"),
                H("The parity-dependent number of rounds"),
                StatementSource.FromAuthor(Disp(GateBoundFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The multiplier is n minus one when n is even, and n when n is odd, as in the source's conjecture "
                    + "(J_shaping.tex, lines 919-927). Subtraction occurs in the natural numbers before Nat.cast includes the result in the reals. "
                    + "Thus the definition also gives zero at n = 0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The upper bound for every coupling matrix"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Local("claim"), Qualified("Prop")), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least two and every real symmetric n by n matrix M with zero diagonal, "
                    + "there is a feasible nonnegative schedule whose total weight is at most gateBound(n) times offDiagSup(M). "
                    + "This states the upper-bound part of the source's conjecture for every M "
                    + "(J_shaping.tex, lines 240 and 919-927). Tightness is the source's Theorem prop:worst_case_sol "
                    + "(lines 1121-1130), which is cited rather than re-proved."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A schedule from round-robin matchings"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First partition all pairs i < j into K matchings, with K = n - 1 for even n and K = n for odd n. "
                        + "For even n identify the vertices with an extra point and ZMod(n - 1), and label the rounds by ZMod(n - 1). "
                        + "Color a pair of finite vertices x,y by x + y, and a pair consisting of the extra point and x by x + x. "
                        + "Addition is cancellative, and doubling is injective because n - 1 is odd. "
                        + "These facts show that distinct edges sharing a vertex have different colors. "
                        + "For odd n identify the vertices and rounds with ZMod n and color x,y by x + y; cancellation again gives the same property. "
                        + "In each case the color is symmetric in the endpoints. Orienting every edge by i < j therefore gives disjoint matching classes, "
                        + "and every such pair belongs to exactly one class.")),
                    Paragraph(Text(
                        "For a Boolean function s write its ith real sign as (-1) to the power Bool.toNat(s(i)). "
                        + "Flipping the bits in a fixed set of vertices is an involution and negates exactly those signs. "
                        + "Consequently, any real function of s that changes sign under this involution has sum zero over all s.")),
                    Paragraph(Text(
                        "For a matching R and real coefficients c(i,j), consider the product over its edges of "
                        + "1 + c(i,j) times the ith and jth signs. Flipping whole edges and unmatched singleton vertices leaves this product unchanged. "
                        + "If i < j is absent from R, choose the block containing i: it is either its matching edge or the unmatched singleton. "
                        + "This block excludes j. Flipping it preserves the product but negates the product of the ith and jth signs, "
                        + "so the corresponding weighted pair sum is zero.")),
                    Paragraph(Text(
                        "The sum of the product weights is 2 to the power n. To see this, induct on the matching. "
                        + "For the empty matching every weight is one. On inserting an edge, expand its factor: "
                        + "the extra term is its coefficient times the absent-pair sum for the smaller matching, which is zero. "
                        + "For a pair belonging to R, erase that edge and expand its factor in the weighted pair sum. "
                        + "The absent-pair term vanishes, and the square of each sign is one. "
                        + "The remaining term is c(i,j) times 2 to the power n.")),
                    Paragraph(Text(
                        "When the absolute values of the coefficients are at most one, every product factor is nonnegative. "
                        + "Divide the weights by the positive real number 2 to the power n. "
                        + "The resulting probability law has pair moment c(i,j) on R and zero on every other pair i < j.")),
                    Paragraph(Text(
                        "Next fold any nonnegative law onto SignVec n. At the final coordinate n - 1, inspect its Boolean value. "
                        + "If it is true, complement every bit; otherwise leave every bit unchanged. "
                        + "The final bit is then false, and complementing all bits preserves every pair of signs. "
                        + "Sum the original weights over each fiber of this map. The finite pushforward is nonnegative, "
                        + "preserves the total mass, and preserves every pair moment.")),
                    Paragraph(Text(
                        "Set d = offDiagSup(M). The maximum contains zero, so d is nonnegative, and each absolute entry with i < j is at most d. "
                        + "If d = 0, all these entries vanish and the constant zero schedule is feasible with total weight zero. "
                        + "Otherwise d is positive, and the normalized coefficients c(i,j) = M(i,j)/d have absolute value at most one. "
                        + "For every matching class choose the probability law just constructed. Multiply their sum by d, then fold this nonnegative law onto SignVec n.")),
                    Paragraph(Text(
                        "For each i < j, exactly one matching class contains the pair. Its contribution to the pair moment is M(i,j)/d, "
                        + "and all other classes contribute zero. Multiplication by d and preservation of pair moments under folding give precisely M(i,j), "
                        + "so the folded weights are feasible. Each class has mass one, hence their scaled sum has mass d times the real cast of K. "
                        + "Folding preserves this mass, which equals gateBound(n) times offDiagSup(M) and in particular satisfies the asserted inequality. "
                        + "The construction uses only the strictly upper triangular entries; symmetry and the zero diagonal specify the coupling matrices in the claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bassler-heinrich-kliesch-2024-global-zz-gate-time-bound"),
                    ResolutionKind.Proved)))));

    private static Formula SignVecFormula() => All("n", Naturals(),
        Equal(Typed(LocalCall("SignVec", X("n")), Qualified("Type")),
            At(Qualified("Subtype"), LambdaOf("s", Arrow(FinOf(X("n")), Qualified("Bool")),
                All("i", FinOf(X("n")), Arrow(
                    Equal(Add(At(Qualified("Fin", "val"), X("i")), Typed(D(1), Naturals())), X("n")),
                    Equal(At(X("s"), X("i")), Qualified("false"))))))));

    private static Formula IsFeasibleFormula()
    {
        Formula nonnegative = All("m", LocalCall("SignVec", X("n")),
            LE(Typed(D(0), Reals()), At(X("lam"), X("m"))));
        Formula moments = All("i", FinOf(X("n")), All("j", FinOf(X("n")), Arrow(LT(X("i"), X("j")),
            Equal(At(X("M"), X("i"), X("j")),
                SumOver("m", LocalCall("SignVec", X("n")),
                    Mul(At(X("lam"), X("m")), Parenthesized(Mul(SignAt("i"), SignAt("j")))))))));
        return All("n", Naturals(), All("M", MatrixType(),
            All("lam", Arrow(LocalCall("SignVec", X("n")), Reals()),
                Equal(Typed(LocalCall("IsFeasible", X("M"), X("lam")), Qualified("Prop")), And(nonnegative, moments)))));
    }

    private static Formula OffDiagSupFormula()
    {
        Formula pairType = At(Qualified("Prod"), FinOf(X("n")), FinOf(X("n")));
        Formula first = At(Qualified("Prod", "fst"), X("e"));
        Formula second = At(Qualified("Prod", "snd"), X("e"));
        Formula value = At(Qualified("Option", "elim"), X("p"), Typed(D(0), Reals()),
            LambdaOf("e", pairType, At(Qualified("ite"), LT(first, second),
                new Formula.Absolute(At(X("M"), first, second)), Typed(D(0), Reals()))));
        return All("n", Naturals(), All("M", MatrixType(),
            Equal(Typed(LocalCall("offDiagSup", X("M")), Reals()),
                Seq(new Formula.Subscript(Max, Seq(Typed(X("p"), At(Qualified("Option"), pairType)))),
                    Sp, Parenthesized(value)))));
    }

    private static Formula GateBoundFormula() => All("n", Naturals(),
        Equal(Typed(LocalCall("gateBound", X("n")), Reals()),
            Typed(At(Qualified("Nat", "cast"), Typed(
                At(Qualified("ite"), At(Qualified("Even"), X("n")),
                    Parenthesized(Subtract(X("n"), Typed(D(1), Naturals()))), X("n")), Naturals())), Reals())));

    private static Formula ClaimBody()
    {
        Formula schedule = Some("lam", Arrow(LocalCall("SignVec", X("n")), Reals()),
            And(LocalCall("IsFeasible", X("M"), X("lam")),
                LE(SumOver("m", LocalCall("SignVec", X("n")), At(X("lam"), X("m"))),
                    Mul(LocalCall("gateBound", X("n")), LocalCall("offDiagSup", X("M"))))));
        Formula zeroDiagonal = All("i", FinOf(X("n")),
            Equal(At(X("M"), X("i"), X("i")), Typed(D(0), Reals())));
        return All("n", Naturals(), Arrow(LE(Typed(D(2), Naturals()), X("n")),
            All("M", MatrixType(), Arrow(At(Qualified("Matrix", "IsSymm"), X("M")), Arrow(zeroDiagonal, schedule)))));
    }

    private static Formula SignAt(string index) => new Formula.Power(
        Parenthesized(new Formula.Negate(Typed(D(1), Reals()))),
        At(Qualified("Bool", "toNat"), At(At(Qualified("Subtype", "val"), X("m")), X(index))));
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(X("n")), FinOf(X("n")), Reals());
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Optimization", "GlobalZZGateTimeBound", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => Multiply(Parenthesized(left), Parenthesized(right));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
}
