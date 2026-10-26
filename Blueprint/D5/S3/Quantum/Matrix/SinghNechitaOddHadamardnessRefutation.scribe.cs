using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class SinghNechitaOddHadamardnessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/singhnechita2022evolution");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The proposed odd-order minimum of Hadamardness cannot be attained in order nine.",
        H("An obstruction to the odd-order Hadamardness minimum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("singh-nechita-sign-matrix"),
                DeclarationHandle.Create(Prefix + "IsSignMatrix"),
                H("Integer sign matrices"),
                StatementSource.FromAuthor(Disp(SignMatrixFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A sign matrix is a square integer matrix whose entries are all one or minus one. "
                        + "The indices i and j range over Fin d. This is the sign-matrix domain in "
                        + "line 779 of the source, with the real signs represented exactly as integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("singh-nechita-hadamardness"),
                DeclarationHandle.Create(Prefix + "hadamardness"),
                H("The trace of the squared row Gram matrix"),
                StatementSource.FromAuthor(Disp(HadamardnessFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Hadamardness is the trace of the square of the row Gram matrix c cᵀ. "
                        + "The definition is meaningful for every square integer matrix c, without a sign hypothesis. "
                        + "For sign matrices it is the integer-valued form of the measure in equation "
                        + "eq:Hada_measure, lines 780–783 of the source. Real sign matrices have conjugate "
                        + "transpose equal to transpose, so the integer trace has the same value as the real trace."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("singh-nechita-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed minimum in every odd order"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every odd natural d, some sign matrix c attains d cubed plus d times (d minus one), "
                        + "and every sign matrix b has Hadamardness at least that value. "
                        + "Together these clauses say that the value is the minimum over sign matrices. "
                        + "They express the conjecture in line 848 of the source. The entire expression "
                        + "d^3 + d*(d−1) is evaluated in the natural numbers, including natural subtraction, "
                        + "and then cast to the integers in both the equality and the lower bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("singh-nechita-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Nonattainment in order nine"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a sign matrix c of order nine, put G = c cᵀ. Symmetry of G gives "
                            + "trace(GG) = Σᵢ Σⱼ Gᵢⱼ², by expressing the trace as the dot product of the "
                            + "vectorized Gram matrix with itself. Each diagonal entry Gᵢᵢ is nine, since "
                            + "it is the sum of nine squared signs. Every entry Gᵢⱼ is one modulo two, "
                            + "since each of its nine summands is a product of two signs.")),
                    Paragraph(Text(
                        "Suppose the Hadamardness of c is 801. Each diagonal square Gᵢᵢ² equals 81; "
                            + "every off-diagonal Gᵢⱼ is nonzero by its residue modulo two, so its square "
                            + "is at least one. These lower bounds sum to 9·81 + 9·8 = 801. Equality of "
                            + "the total sums forces equality first in every row sum and then in every "
                            + "individual summand. Thus each off-diagonal Gᵢⱼ has square one and is a sign.")),
                    Paragraph(Text(
                        "For any three rows indexed by i, j and r, sign arithmetic modulo four gives "
                            + "Gᵢⱼ = Gᵢᵣ + Gᵣⱼ − 1 modulo four: the corresponding identity holds in each "
                            + "column, and the nine subtracted ones sum to one modulo four. Set s(0)=1 "
                            + "and s(i)=Gᵢ₀ for i≠0, and let b = diagonal(s)c. Every s(i) is a sign, "
                            + "so b is a sign matrix and (bbᵀ)ᵢⱼ = s(i)s(j)Gᵢⱼ. Its off-diagonal entries "
                            + "are signs, and (bbᵀ)ᵢ₀ = Gᵢ₀² = 1 for i≠0. Symmetry supplies the same "
                            + "identity in row zero. For distinct nonzero i and j, the preceding "
                            + "congruence with r=0 makes (bbᵀ)ᵢⱼ equal to one modulo four, excluding "
                            + "minus one. Its diagonal entries are nine. Therefore bbᵀ = 8I + J, "
                            + "where J is the matrix with every entry one.")),
                    Paragraph(Text(
                        "Map b entrywise from the integers to ZMod 3, obtaining a. Let u and v be "
                            + "the vectors of length nine with constant entries two and one in ZMod 3. "
                            + "The mapped identity is aaᵀ = 2(I + uvᵀ), with uvᵀ expressed as the product "
                            + "of the single column u and the single row v indexed by Unit. Taking "
                            + "determinants and using the determinant formula for a rank-one addition "
                            + "to the identity yields det(a)² = 2⁹(1 + Σᵢ v(i)u(i)) = 2 in ZMod 3. "
                            + "No element z of ZMod 3 has square two: taking the natural representative "
                            + "z.val would give a natural square congruent to two modulo three, whereas "
                            + "natural squares have residue zero or one. This is a contradiction.")),
                    Paragraph(Text(
                        "If claim held, its instance at the odd natural number nine would provide "
                            + "a sign matrix c with Hadamardness 9³ + 9·(9−1) = 801. The preceding "
                            + "argument rules out such a matrix, so claim is false. Its additional "
                            + "lower-bound clause is unnecessary for this contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("singh-nechita-2022-odd-hadamardness"),
                    ResolutionKind.Refuted)))));

    private static Formula SignMatrixFormula() => All("d", Naturals(), All("c", MatrixType(),
        Equivalence(LocalCall("IsSignMatrix", F.Id("c")),
            All("i", FinOf(F.Id("d")), All("j", FinOf(F.Id("d")),
                Disjunction(Equal(At(F.Id("c"), F.Id("i"), F.Id("j")), Typed(D(1), Integers())),
                    Equal(At(F.Id("c"), F.Id("i"), F.Id("j")),
                        new Formula.Negate(Typed(D(1), Integers())))))))));

    private static Formula HadamardnessFormula()
    {
        Formula gram = Multiply(F.Id("c"), At(Qualified("Matrix", "transpose"), F.Id("c")));
        return All("d", Naturals(), All("c", MatrixType(),
            Equal(Typed(LocalCall("hadamardness", F.Id("c")), Integers()),
                At(Qualified("Matrix", "trace"), Multiply(gram, gram)))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d");
        Formula value = Typed(At(Qualified("Nat", "cast"), Typed(
            Add(new Formula.Power(d, D(3)), Multiply(d, Subtract(d, D(1)))), Naturals())), Integers());
        Formula minimum = Conjunction(LocalCall("IsSignMatrix", F.Id("c")),
            Conjunction(Equal(LocalCall("hadamardness", F.Id("c")), value),
                All("b", MatrixType(), Arrow(LocalCall("IsSignMatrix", F.Id("b")),
                    LE(value, LocalCall("hadamardness", F.Id("b")))))));
        return Equivalence(Local("claim"), All("d", Naturals(),
            Arrow(At(Qualified("Odd"), d), Some("c", MatrixType(), minimum))));
    }

    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Matrix",
        "SinghNechitaOddHadamardnessRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula MatrixType() => At(Qualified("Matrix"),
        FinOf(F.Id("d")), FinOf(F.Id("d")), Integers());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Disjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
