using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class LevensPascalianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Galois/LevensPascalian.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/levens2025pascalian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square discriminant of the degree twenty-four binomial truncation refutes the odd-index Galois-group conjecture at n = 49.",
        H("A square-discriminant obstruction for the Pascalian polynomial of degree 49"),
        Blocks(
            Node("polynomial", "The Pascalian polynomial", "P", PFormula(),
                "Section 1, printed page 1: “let ⟨n k⟩ = C(n, ⌊(n−k)/2⌋) for 0 ≤ k ≤ n, call the ⟨n k⟩ triangle the Pascalian numbers, and let the nth Pascalian polynomial be P_n(z) = Σ_{k=0}^{n} ⟨n k⟩ z^{n−k}.” The coefficient binomial is Nat.choose, cast into ℚ and then embedded by Polynomial.C. The index k ranges from zero through n; subtraction and Nat.div are operations on ℕ, so Nat.div (n − k) 2 is the floor in this range.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sign-flip", "Sign change on the signed letters", "signFlip", SignFlipFormula(),
                "The two Boolean values represent the two signs. Equiv.prodCongr fixes the Fin m coordinate and swaps false with true.",
                AssessedProvenance.FromRepo()),
            Node("hyperoctahedral", "The group of signed permutations", "hyperoctahedral", HyperoctahedralFormula(),
                "The mth hyperoctahedral group is represented as the subgroup of permutations of Fin m × Bool commuting with signFlip m. This centralizer has order 2^m m!.",
                AssessedProvenance.FromRepo()),
            Node("claim", "Levens Conjecture 6.4, odd-index clause", "claim",
                Equal(Local("claim"), Parenthesized(ClaimBody())),
                "Conjecture 6.4, printed page 20: “P_n(z) has full Galois group for even n. For n = 2m + 1, the Galois group of P_n(z) is the mth hyperoctahedral group.” The displayed proposition is the second sentence, for natural m ≥ 1. Polynomial.Gal is the automorphism group of the splitting field over ℚ. Being the indicated group means the existence of an abstract multiplicative equivalence, expressed by Nonempty; disproving this also excludes an isomorphism as permutation groups.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("levens-pascalian-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The odd-index assertion is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "At m = 24, put c = 63205303218876 = Nat.choose 49 24 and q(X) = ∑ j ∈ Finset.range 25, Polynomial.C ((Nat.choose 49 j : ℕ) : ℚ) * X^j. Then P 49 = (1 + X) * q.comp (X^2), and (1 + X) * q.derivative − Polynomial.C 49 * q = −Polynomial.C (25*c) * X^24. Resultant identities give q.discr = (7 * 5^23 * c^11)^2. These polynomial and rational identities are checked inside the proof.")),
                    Paragraph(Text(
                        "The Vandermonde determinant of the twenty-four distinct roots of q is rational and nonzero. Every field automorphism fixes it, so its permutation of those roots has sign one. The roots of P 49 are −1 and the signed square roots of the roots of q. Encoding an automorphism by its twenty-four signs and its even permutation is injective. Consequently the Galois group has order at most 2^24 * |alternatingGroup (Fin 24)|, strictly less than the hyperoctahedral order 2^24 * 24!.")),
                    Paragraph(Text(
                        "This excludes the abstract group isomorphism at n = 49. It does not determine the exact Galois group. The even-index sentence, Conjecture 6.3, and a classification of the other odd indices remain separate questions. The square-discriminant formula is classical; its general form appears in Filaseta–Moy, Lemma 3, as recorded with the source reference."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("levens-2025-pascalian-galois-square-discriminant"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("levens-pascalian-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PFormula()
    {
        Formula n = X("n");
        Formula k = X("k");
        Formula difference = new Formula.Binary(n, FormulaBinaryOperator.Subtract, k);
        Formula coefficient = At(Q("Polynomial", "C"), Typed(
            At(Q("Nat", "choose"), n, At(Q("Nat", "div"), difference, D(2))), Rationals()));
        Formula index = Seq(k, Sp, InMacro, Sp,
            At(Q("Finset", "range"), new Formula.Binary(n, FormulaBinaryOperator.Add, D(1))));
        Formula body = new Formula.Binary(coefficient, FormulaBinaryOperator.Multiply,
            new Formula.Power(Q("Polynomial", "X"), difference));
        return All("n", Naturals(), Equal(At(Local("P"), n),
            Seq(new Formula.Subscript(Sum, index), Sp, Parenthesized(body))));
    }

    private static Formula SignFlipFormula() => All("m", Naturals(),
        Equal(At(Local("signFlip"), X("m")), At(Q("Equiv", "prodCongr"),
            At(Q("Equiv", "refl"), At(Q("Fin"), X("m"))),
            At(Q("Equiv", "swap"), Q("false"), Q("true")))));

    private static Formula HyperoctahedralFormula() => All("m", Naturals(),
        Equal(At(Local("hyperoctahedral"), X("m")),
            At(Q("Subgroup", "centralizer"), new Formula.SetLiteral([At(Local("signFlip"), X("m"))]))));

    private static Formula ClaimBody() => All("m", Naturals(),
        new Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, X("m"))),
            FormulaLogicOperator.Implies,
            Parenthesized(At(Q("Nonempty"), At(Q("MulEquiv"),
                QGal(At(Local("P"), new Formula.Binary(
                    new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, X("m")),
                    FormulaBinaryOperator.Add, D(1)))),
                At(Local("hyperoctahedral"), X("m")))))));

    private static Formula QGal(Formula p) => At(Q("Polynomial", "Gal"), p);
    private static Formula Local(string name) => Q("D5", "S3", "Factorization", "Galois", "LevensPascalian", name);
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula X(string name) => F.Id(name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(X("Q")));
}
