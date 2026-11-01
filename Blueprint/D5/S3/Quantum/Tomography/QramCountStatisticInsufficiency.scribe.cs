using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class QramCountStatisticInsufficiencyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/bohac2025biasclassqram");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two queries to a fixed four-address memory contain discrimination information beyond the plus count.",
        H("Insufficiency of the plus-count statistic"),
        Blocks(
            Definition("weight", "weight", "The weight of a Boolean memory", WeightFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The weight of f is the number of addresses at which f is true. "
                    + "This is the Hamming weight in bias_class_discrimination.tex, lines 244–250. "
                    + "Addresses are indexed by Fin (2^n), and the definition includes n = 0."),
            Definition("weight-class", "weightClass", "An exact-weight class", WeightClassFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The class consists of all Boolean memories on 2^n addresses with weight m, "
                    + "as in bias_class_discrimination.tex, lines 244–250. The finite set is empty when m exceeds 2^n."),
            Definition("address-state", "addressState", "The phase address state", AddressStateFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The coordinate at x is the sign determined by f(x), divided by the square root of the number of addresses. "
                    + "This is the address state in bias_class_discrimination.tex, lines 169–174. "
                    + "Bool.toNat converts false and true to zero and one. The power 2^n inside Real.sqrt is real; "
                    + "Complex.ofReal includes that real square root into the complex scalars."),
            Definition("plus-state", "plusState", "The all-plus address state", PlusStateFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The identically false memory gives the uniform all-plus vector. "
                    + "The source defines this vector in bias_class_discrimination.tex, line 165, "
                    + "and relates it to the address state in line 174. Function.const specifies the constant Boolean memory."),
            Definition("copy-state", "copyState", "Several copies of one sampled memory", CopyStateFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Average the t-fold product of the address-state projectors over the uniform exact-weight class. "
                    + "The same f occurs in every register: the memory is sampled once and held fixed, "
                    + "as in bias_class_discrimination.tex, lines 255–256 and 395–400. "
                    + "A row or column is a function from Fin t to Fin (2^n). "
                    + "The natural class cardinality is cast to a complex scalar before division. "
                    + "The formula is defined for all natural n, t and m; an empty class gives the zero matrix."),
            Definition("plus-proj", "plusProj", "The single-register plus projector", PlusProjFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The outer product of the all-plus vector with its conjugate is the plus projector. "
                    + "It is the first effect of the two-outcome measurement in bias_class_discrimination.tex, line 405. "
                    + "The star on a vector acts coordinatewise."),
            Definition("count-proj", "countProj", "The projector for an exact plus count", CountProjFormula(),
                AssessedProvenance.FromRepo(Source),
                "For each k-element subset s of the registers, use the plus projector at sites in s "
                    + "and its complementary projector at the remaining sites, then sum these tensor-product effects. "
                    + "This constructs the exact-count effect for the measurement of bias_class_discrimination.tex, lines 404–415. "
                    + "The matrix entries are products over the registers. For k greater than t the sum is empty."),
            Definition("success-prob", "successProb", "Equal-prior success of a binary test", SuccessProbFormula(),
                AssessedProvenance.FromRepo(Source),
                "The effect e accepts weight m₀ and the complementary effect accepts weight m₁. "
                    + "Their Born readouts, each weighted by one half, give the equal-prior success probability. "
                    + "The equal-prior discrimination setting is that of bias_class_discrimination.tex, lines 327–345; "
                    + "this formula applies it to the t-copy states. Taking real parts makes the expression "
                    + "a real number for arbitrary e; its probability interpretation requires e and 1 − e to be positive semidefinite "
                    + "and both weights to lie between zero and 2^n."),
            Definition("count-test", "countTest", "A deterministic count decision", CountTestFormula(),
                AssessedProvenance.FromRepo(Source),
                "A Boolean rule g accepts the first weight exactly for those counts at which it is true. "
                    + "Sum the corresponding exact-count projectors over k : Fin (t + 1). "
                    + "Fin.val explicitly converts this finite index to the natural argument of countProj."),
            Definition("claim", "claim", "Sufficiency for every equal-prior test", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For every positive n and t, every pair of admissible weights and every effect e with "
                    + "both e and 1 − e positive semidefinite, ask whether a deterministic count rule achieves "
                    + "at least the success of e. This is an equal-prior reading of the count-sufficiency question "
                    + "in bias_class_discrimination.tex, lines 454–457."),
            Describe.Lean(
                DescribeId.Create("qram-count-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Four addresses and two copies suffice for a strict gap"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take n = 2, t = 2, m₀ = 1 and m₁ = 2. In coordinate order 0, 1, 2, 3, "
                            + "let h₀ = (1,1,1,1)/2, h₁ = (1,−1,1,−1)/2, "
                            + "h₂ = (1,1,−1,−1)/2 and h₃ = (1,−1,−1,1)/2. "
                            + "Their inner products are one for equal indices and zero otherwise, and h₀ is plusState 2. "
                            + "Put vᵧ𝓏(x) = hᵧ(x(0))h𝓏(x(1)), R = Σᵧ₌₁³ vᵧᵧvᵧᵧ† and E = 1 − R. "
                            + "Thus E accepts weight one unless the two Walsh outcomes are equal and nonzero.")),
                    Paragraph(Text(
                        "The weight-one class consists of the four memories with one true entry; "
                            + "the weight-two class consists of the six memories with two true entries. "
                            + "Inner products of product vectors factor into products of single-register inner products. "
                            + "For vectors u and v, trace((uu†)(vv†)) = (u†v)(v†u). "
                            + "Each weight-one address state has squared overlap 1/4 with every hᵧ. "
                            + "Factoring the two-register overlaps and averaging over the four memories therefore gives "
                            + "trace(copyState 2 2 1 · vᵧ𝓏vᵧ𝓏†) = 1/16 for every y and z.")),
                    Paragraph(Text(
                        "For weight two, the supports {0,1}, {0,2}, {0,3}, {1,2}, {1,3} and {2,3} "
                            + "give address states −h₂, −h₁, −h₃, h₃, h₁ and h₂, respectively. "
                            + "The signs cancel in the two-copy projectors, giving copyState 2 2 2 = R/3. "
                            + "The product vectors vᵧ𝓏 are orthonormal, so R† = R and R² = R. "
                            + "Consequently E†E = E and R†R = R; each is a Gram matrix and hence positive semidefinite. "
                            + "Thus both E and 1 − E are positive semidefinite.")),
                    Paragraph(Text(
                        "Every four-address phase state has norm one. Factoring the tensor inner products and "
                            + "averaging gives trace(copyState 2 2 1) = 1. "
                            + "The three orthonormal summands of R give trace(R) = 3, "
                            + "so trace(copyState 2 2 2) = 1 as well. "
                            + "The flat weight-one outcome law gives trace(copyState 2 2 1 · R) = 3/16, "
                            + "whereas copyState 2 2 2 = R/3 and R² = R give trace(copyState 2 2 2 · R) = 1. "
                            + "Substituting E = 1 − R into successProb yields (1/2)(1 − 3/16) + (1/2) = 29/32.")),
                    Paragraph(Text(
                        "The weight-two Walsh outcome law is 1/3 for y = z ≠ 0 and zero otherwise. "
                            + "Since 1 − plusProj 2 is the sum of the three nonzero Walsh projectors, "
                            + "countProj 2 2 k is the sum of the projectors vᵧ𝓏vᵧ𝓏† whose pair of labels "
                            + "contains exactly k zeros. Summing the two outcome laws gives count probabilities "
                            + "(9/16, 3/8, 1/16) for weight one and (1, 0, 0) for weight two, "
                            + "in count order 0, 1, 2. Expanding successProb for countTest and evaluating "
                            + "the eight choices of g(0), g(1), g(2) bounds every deterministic count rule by 23/32.")),
                    Paragraph(Text(
                        "If claim held, its specialization to these parameters and the valid effect E "
                            + "would supply a count rule g with 29/32 ≤ successProb 2 2 1 2 (countTest 2 2 g). "
                            + "The bound 23/32 contradicts this inequality. Hence claim is false. "
                            + "This strict gap establishes insufficiency of the plus count; it does not determine "
                            + "the optimal collective success or the error exponent asked for in the same remark."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bohac-2025-qram-count-statistic-insufficiency"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create("qram-count-" + id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula WeightFormula() => All("n", Naturals(), All("f", Memories(),
        Equal(Typed(LocalCall("weight", X("f")), Naturals()),
            At(Qualified("Finset", "card"), At(Qualified("Finset", "filter"),
                LambdaOf("x", Addresses(), Equal(At(X("f"), X("x")), Qualified("Bool", "true"))),
                Universe(Addresses()))))));

    private static Formula WeightClassFormula() => All("n", Naturals(), All("m", Naturals(),
        Equal(Typed(LocalCall("weightClass", X("n"), X("m")), FinsetOf(Memories())),
            At(Qualified("Finset", "filter"),
                LambdaOf("f", Memories(), Equal(LocalCall("weight", X("f")), X("m"))), Universe(Memories())))));

    private static Formula AddressStateFormula()
    {
        Formula sign = new Formula.Power(Typed(new Formula.Negate(D(1)), Complexes()),
            At(Qualified("Bool", "toNat"), At(X("f"), X("x"))));
        Formula root = At(Qualified("Complex", "ofReal"), At(Qualified("Real", "sqrt"),
            new Formula.Power(Typed(D(2), Reals()), X("n"))));
        return All("n", Naturals(), All("f", Memories(),
            Equal(Typed(LocalCall("addressState", X("n"), X("f")), Arrow(Addresses(), Complexes())),
                LambdaOf("x", Addresses(), new Formula.Fraction(sign, root)))));
    }

    private static Formula PlusStateFormula() => All("n", Naturals(),
        Equal(Typed(LocalCall("plusState", X("n")), Arrow(Addresses(), Complexes())),
            LocalCall("addressState", X("n"), At(Qualified("Function", "const"),
                Addresses(), Qualified("Bool", "false")))));

    private static Formula CopyStateFormula()
    {
        Formula card = At(Qualified("Finset", "card"), LocalCall("weightClass", X("n"), X("m")));
        Formula scalar = new Formula.Fraction(Typed(D(1), Complexes()),
            Typed(At(Qualified("Nat", "cast"), card), Complexes()));
        Formula entry = ProductOver("i", FinOf(X("t")), Multiply(
            LocalCall("addressState", X("n"), X("f"), At(X("x"), X("i"))),
            At(Qualified("star"), LocalCall("addressState", X("n"), X("f"), At(X("y"), X("i"))))));
        Formula matrix = At(Qualified("Matrix", "of"),
            LambdaOf("x", CopyIndices(), LambdaOf("y", CopyIndices(), entry)));
        return All("n", Naturals(), All("t", Naturals(), All("m", Naturals(),
            Equal(Typed(LocalCall("copyState", X("n"), X("t"), X("m")), CopyMatrix()),
                Smul(scalar, SumIn("f", LocalCall("weightClass", X("n"), X("m")), matrix))))));
    }

    private static Formula PlusProjFormula() => All("n", Naturals(),
        Equal(Typed(LocalCall("plusProj", X("n")), AddressMatrix()),
            At(Qualified("Matrix", "vecMulVec"), LocalCall("plusState", X("n")),
                At(Qualified("star"), LocalCall("plusState", X("n"))))));

    private static Formula CountProjFormula()
    {
        Formula effect = At(Qualified("ite"), Member(X("i"), X("s")), LocalCall("plusProj", X("n")),
            Subtract(Typed(D(1), AddressMatrix()), LocalCall("plusProj", X("n"))));
        Formula entry = ProductOver("i", FinOf(X("t")),
            At(Parenthesized(effect), At(X("x"), X("i")), At(X("y"), X("i"))));
        Formula matrix = At(Qualified("Matrix", "of"),
            LambdaOf("x", CopyIndices(), LambdaOf("y", CopyIndices(), entry)));
        Formula subsets = At(Qualified("Finset", "powersetCard"), X("k"), Universe(FinOf(X("t"))));
        return All("n", Naturals(), All("t", Naturals(), All("k", Naturals(),
            Equal(Typed(LocalCall("countProj", X("n"), X("t"), X("k")), CopyMatrix()),
                SumIn("s", subsets, matrix)))));
    }

    private static Formula SuccessProbFormula()
    {
        Formula half = Typed(new Formula.Fraction(D(1), D(2)), Reals());
        Formula first = At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"),
            Multiply(LocalCall("copyState", X("n"), X("t"), X("m₀")), X("e"))));
        Formula second = At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"),
            Multiply(LocalCall("copyState", X("n"), X("t"), X("m₁")),
                Subtract(Typed(D(1), CopyMatrix()), X("e")))));
        return All("n", Naturals(), All("t", Naturals(), All("m₀", Naturals(), All("m₁", Naturals(),
            All("e", CopyMatrix(), Equal(Typed(Success(X("e")), Reals()),
                Add(Multiply(half, first), Multiply(half, second))))))));
    }

    private static Formula CountTestFormula() => All("n", Naturals(), All("t", Naturals(),
        All("g", CountRules(), Equal(Typed(LocalCall("countTest", X("n"), X("t"), X("g")), CopyMatrix()),
            SumOver("k", FinOf(Add(X("t"), D(1))), At(Qualified("ite"),
                Equal(At(X("g"), X("k")), Qualified("Bool", "true")),
                LocalCall("countProj", X("n"), X("t"), Typed(At(Qualified("Fin", "val"), X("k")), Naturals())),
                Typed(D(0), CopyMatrix())))))));

    private static Formula ClaimFormula()
    {
        Formula comparison = Some("g", CountRules(), LE(Success(X("e")),
            Success(LocalCall("countTest", X("n"), X("t"), X("g")))));
        Formula effects = All("e", CopyMatrix(), Arrow(At(Qualified("Matrix", "PosSemidef"), X("e")),
            Arrow(At(Qualified("Matrix", "PosSemidef"), Subtract(Typed(D(1), CopyMatrix()), X("e"))), comparison)));
        Formula weights = All("m₀", Naturals(), All("m₁", Naturals(),
            Arrow(LE(X("m₀"), AddressCount()), Arrow(LE(X("m₁"), AddressCount()), effects))));
        return Equal(Typed(Local("claim"), Qualified("Prop")),
            Parenthesized(All("n", Naturals(), Arrow(LE(D(1), X("n")),
                All("t", Naturals(), Arrow(LE(D(1), X("t")), weights))))));
    }

    private static Formula Success(Formula effect) =>
        LocalCall("successProb", X("n"), X("t"), X("m₀"), X("m₁"), effect);
    private static Formula AddressCount() => new Formula.Power(Typed(D(2), Naturals()), X("n"));
    private static Formula Addresses() => FinOf(AddressCount());
    private static Formula Memories() => Arrow(Addresses(), Qualified("Bool"));
    private static Formula CopyIndices() => Arrow(FinOf(X("t")), Addresses());
    private static Formula AddressMatrix() => At(Qualified("Matrix"), Addresses(), Addresses(), Complexes());
    private static Formula CopyMatrix() => At(Qualified("Matrix"), CopyIndices(), CopyIndices(), Complexes());
    private static Formula CountRules() => Arrow(FinOf(Add(X("t"), D(1))), Qualified("Bool"));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), Parenthesized(size));
    private static Formula FinsetOf(Formula type) => At(Qualified("Finset"), Parenthesized(type));
    private static Formula Universe(Formula type) => Typed(Qualified("Finset", "univ"), FinsetOf(type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Tomography",
        "QramCountStatisticInsufficiency", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch
    {
        "m₀" => new Formula.Subscript(F.Id("m"), D(0)),
        "m₁" => new Formula.Subscript(F.Id("m"), D(1)),
        _ => F.Id(name),
    };
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
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(X(name), set)), Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula matrix) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
}
