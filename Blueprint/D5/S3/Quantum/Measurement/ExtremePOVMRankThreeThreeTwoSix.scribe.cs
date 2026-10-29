using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ExtremePOVMRankThreeThreeTwoSixDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/haapasalopellonpaa2020extreme");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit extreme eight-outcome POVM on complex seven-space refutes the proposed rank-vector exclusion.",
        H("An extreme POVM with rank vector (3,3,2,2,2,2,2,2)"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("extreme-povm-rank-three-three-two-six-is-extreme"),
                DeclarationHandle.Create(Module + ".IsExtreme"),
                H("Midpoint extremality of a finite POVM"),
                StatementSource.FromAuthor(Disp(IsExtremeFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "An n-outcome family of complex 7 by 7 matrices is extreme when it is a POVM and "
                        + "every midpoint decomposition into two POVMs has both factors equal to the original family. "
                        + "This is the midpoint formulation of extremality in Haapasalo and Pellonpää, lines 148–152."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("extreme-povm-rank-three-three-two-six-big-ranks"),
                DeclarationHandle.Create(Module + ".bigRanks"),
                H("Ranks after omitting rank-one outcomes"),
                StatementSource.FromAuthor(Disp(BigRanksFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "bigRanks maps the finite outcome index set to the natural ranks of the effects and filters out "
                        + "all ranks below two. It is the multiset form of the source's rank vector convention, which "
                        + "orders ranks with repetition and omits rank-one outcomes (lines 219–222)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("extreme-povm-rank-three-three-two-six-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The proposed rank-vector exclusion"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Local("claim"), PropType()), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The formal claim says that every extreme finite POVM on complex seven-space has a big-rank multiset "
                        + "different from two rank-three effects followed by six rank-two effects. This is the negative "
                        + "existence question for the problematic vector (3₂,2₆)₇ named in the source at lines 307–314."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("extreme-povm-rank-three-three-two-six-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("An explicit counterexample to the exclusion"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The construction uses the ordered coordinates (e₀,e₁,e₂,f₀,f₁,f₂,g) of complex seven-space. "
                            + "Eight blocks of vectors are formed: the three e coordinates, the three f coordinates, "
                            + "two phase-zero and phase-i edge blocks for each of the three pairs of e coordinates, "
                            + "and the corresponding apex blocks containing g. For each block, form the positive matrix "
                            + "effect j by summing b bᴴ over its vectors, and let frame be the sum of all eight effects.")),
                    Paragraph(Text(
                        "A direct exact coordinate calculation writes frame as the displayed Hermitian 7 by 7 matrix. "
                            + "Its positive-semidefinite sum decomposition and an injectivity calculation for its matrix-vector "
                            + "action prove positive definiteness. The positive square-root factorization of a strictly positive "
                            + "matrix then supplies an invertible normalizer with normalizer · frame · normalizerᴴ = 1. "
                            + "Conjugating every effect by this normalizer gives witness; congruence preserves positive semidefiniteness, "
                            + "the conjugated effects sum to the identity, and congruence by an invertible matrix preserves rank.")),
                    Paragraph(Text(
                        "The block-column factorization effect j = columns j · (columns j)ᴴ identifies each effect rank with "
                            + "the cardinality of its block. The two coordinate blocks have cardinality three and the other six "
                            + "blocks cardinality two, so witness has bigRanks equal to the target multiset. For each block, an "
                            + "explicit left inverse of its columns is verified by finite coordinate cases. Expanding the conjugated "
                            + "products therefore reduces independence to the 42 within-block products, whose coefficients are "
                            + "separated by the two phase choices, the apex coordinates, and the coordinate blocks.")),
                    Paragraph(Text(
                        "For a midpoint decomposition of witness into POVMs A and B, positivity and the midpoint equation imply "
                            + "that each A j is supported on the column space of the corresponding block. The left inverse gives a "
                            + "coefficient matrix for A j − witness j, and the normalized expansion expresses the difference as a linear "
                            + "combination of the independent 42 conjugated within-block products. Summing over j gives zero because "
                            + "both families sum to the identity, so every coefficient vanishes. Thus A = witness, and the midpoint equation "
                            + "then gives B = witness. Hence witness is extreme and its target big-rank multiset contradicts claim at n = 8."))),
                DescribeRole.Theorem))));

    private static Formula IsExtremeFormula()
    {
        Formula n = F.Id("n"), M = F.Id("M"), A = F.Id("A"), B = F.Id("B"), j = F.Id("j");
        Formula family = Arrow(Fin(n), MatrixType());
        Formula midpoint = Equal(At(M, j), Smul(HalfComplex(), Add(At(A, j), At(B, j))));
        Formula decomposition = All("j", Fin(n), midpoint);
        Formula body = And(IsPOVM(M), All("A", family, All("B", family,
            Imp(IsPOVM(A), Imp(IsPOVM(B), Imp(decomposition, And(Equal(A, M), Equal(B, M))))))));
        return All("n", Naturals(), All("M", family, Equal(At(Local("IsExtreme"), M), body)));
    }

    private static Formula BigRanksFormula()
    {
        Formula n = F.Id("n"), M = F.Id("M");
        Formula ranks = At(Qualified("Multiset", "map"),
            LambdaOf("j", Fin(n), At(Qualified("Matrix", "rank"), At(M, F.Id("j")))),
            At(Qualified("Finset", "val"), At(Qualified("Finset", "univ"), Fin(n))));
        Formula filtered = At(Qualified("Multiset", "filter"),
            LambdaOf("r", Naturals(), LE(D(2), F.Id("r"))), ranks);
        return All("n", Naturals(), All("M", Arrow(Fin(n), MatrixType()),
            Equal(At(Local("bigRanks"), M), filtered)));
    }

    private static Formula ClaimBody() => All("n", Naturals(),
        All("M", Arrow(Fin(F.Id("n")), MatrixType()),
            Imp(IsPOVM(F.Id("M")), Imp(At(Local("IsExtreme"), F.Id("M")),
                new Formula.Relation(At(Local("bigRanks"), F.Id("M")), FormulaRelationOperator.NotEqual,
                    ExpectedRanks())))));

    private static Formula ExpectedRanks()
    {
        Formula result = Call("singleton", D(2));
        for (int i = 0; i < 5; i++)
            result = Call("insert", D(2), result);
        result = Call("insert", D(3), result);
        return Call("insert", D(3), result);
    }

    private static Formula IsPOVM(Formula family) => At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
        "ConcealmentKernelNecessityRefutation", "IsPOVM"), family);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurement",
        "ExtremePOVMRankThreeThreeTwoSix", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
                items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        At(Qualified(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(F.Id(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula matrix) =>
        At(Qualified("SMul", "smul"), scalar, matrix);
    private static Formula HalfComplex() =>
        new Formula.Fraction(Typed(D(1), Complexes()), Typed(D(2), Complexes()));
    private static Formula Fin(Formula size) => At(Qualified("Fin"), size);
    private static Formula MatrixType() => At(Qualified("Matrix"), Fin(D(7)), Fin(D(7)), Complexes());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PropType() => F.Id("Prop");
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}
