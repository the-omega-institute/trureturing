using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class FiniteHermitianCongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hermitian matrix over a finite field with nontrivial involution has an identity block and a zero radical in one invertible basis.",
        H("Finite Hermitian Congruence"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-hermitian-congruence"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/FiniteHermitianCongruence.finite_hermitian_congruence"),
            H("Normalized orthogonal basis including the radical"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuadraticForms/fulton1977hermitian")),
            Blocks(
                Paragraph(Text("Let K be any finite field, sigma a ring automorphism of K with sigma(sigma(x))=x for every x and sigma different from the identity, N any natural number, and B an N by N matrix satisfying transpose(map(sigma,B))=B. There is an invertible N by N matrix T with transpose(T) B map(sigma,T) equal to the diagonal matrix whose i-th entry is one when i.val is less than rank(B), and zero otherwise. All matrix entries lie in K. The involution acts entrywise on both B and the same T.")),
                Paragraph(Text("The associated form b(x,y)=x-transpose B sigma(y) is linear in its first argument and sigma-semilinear in its second. It satisfies sigma(b(x,y))=b(y,x). If every b(x,x) were zero, comparing the self-pairings of x+y and x+c y for a scalar c with sigma(c) different from c would force every b(x,y) to vanish. Thus every nonzero form has a nonzero self-pairing.")),
                Paragraph(Text("The pivot value a=b(x,x) lies in the fixed field of sigma. Surjectivity of the finite-field norm and its formula c sigma(c) choose c with c sigma(c)=a-inverse. The vector e=c x then has b(e,e)=1. The kernel of the linear functional y mapped to b(y,e) is complementary to the line K e and orthogonal to e in both arguments. Its dimension is one less, so dimension induction constructs a complete normalized orthogonal basis.")),
                Paragraph(Text("When the restricted form is zero, any basis supplies the remaining radical vectors. The induction starts at dimension zero with the empty basis. Invertibility of the basis matrix T and of its sigma image preserves matrix rank, so the number of unit diagonal entries is exactly rank(B). Singular forms, the zero matrix, and N=0 are included; no orthogonal basis or norm-surjectivity premise is supplied.")),
                Paragraph(Text("This is established finite-field Hermitian-form mathematics. Fulton gives the arbitrary-rank characteristic-two congruence on page 170 of the cited paper. The characteristic-two case is included in the displayed theorem. Its conclusion concerns the matrix congruence; character sums and rank-parity or entropy formulas require additional results."))),
            DescribeRole.Theorem),
            TraceCharacterApplication())));

    private static DocumentBlock TraceCharacterApplication() => new DocumentBlock.Section(
        H("Application: the complete signed trace-character sum"),
        Blocks(
            Paragraph(Text("For this application, let K be any finite field of characteristic two, sigma any nonidentity involutive ring automorphism of K, N any natural number, and B any N by N matrix over K satisfying transpose(map(sigma,B))=B. Put L=NikolovSegal.UnitaryField.fixedField(sigma) and r=rank(B). Vectors are columns indexed by Fin N. The Hermitian identity gives sigma(X-transpose B sigma(X))=X-transpose B sigma(X), so this value defines H_B(X) in L. In the following form and norm equalities, L is identified with its subfield in K; sigma acts entrywise on vectors.")),
            new DocumentBlock.DisplayFormula(ApplicationDefinitions()),
            Paragraph(Text("Equip L with the canonical ZMod.algebra L 2. The trace in the character below is Algebra.trace (ZMod 2) L, from L to the prime field, and val is the representative zero or one. Thus the character takes values in Complex. LanglandsFirstMainLemma.traceAddChar and traceAddChar_ne_one_iff, applied to the nontrivial AddChar.zmodChar on ZMod 2 with value -1 at one, give this nontrivial additive character of L.")),
            new DocumentBlock.DisplayFormula(CharacterDefinition()),
            Paragraph(Text("Use the same invertible T supplied by finite_hermitian_congruence. The substitution X=T Y is a bijection on the vector space of functions from Fin N to K, and sigma(T Y)=map(sigma,T) sigma(Y). Consequently the congruence changes H_B into the sum of exactly r coordinate norms from K to L, with every remaining coordinate absent. The norm here is Algebra.norm L, whose image in K is x sigma(x) by NikolovSegal.UnitaryField.norm_formula.")),
            new DocumentBlock.DisplayFormula(DiagonalNormSum()),
            Paragraph(Text("Write q=|L|. The norm fibre over zero consists only of zero. Each nonzero fibre has q+1 elements: FiniteField.unitsMap_norm_surjective gives surjectivity on units, MonoidHom.card_fiber_eq_of_mem_range identifies their fibre sizes with the kernel, and NikolovSegal.UnitaryField.card_normOne gives that kernel size. AddChar.sum_eq_zero_of_ne_one gives sum over L of psi equal to zero, while psi(0)=1. Grouping the scalar norm sum by these fibres therefore gives the exact negative factor.")),
            new DocumentBlock.DisplayFormula(ScalarNormSum()),
            Paragraph(Text("Additivity of the character turns the diagonal sum into a product of coordinate values. Equiv.sum_comp reindexes by the invertible T, and Fintype.prod_sum factors the sum over all vectors into the coordinate sums. Each of the r norm coordinates contributes -|L| by the scalar calculation; each of the N-r radical coordinates contributes |K| because its character value is psi(0)=1. Hence, with cardinalities cast to Complex, the complete signed sum is")),
            new DocumentBlock.DisplayFormula(SignedTraceSum()),
            Paragraph(Text("This application composes the existing congruence, norm-fibre and character-orthogonality results; it is separate from the displayed Lean congruence theorem. For N=0 the sum and the product are both one. For B=0 the value is |K|^N. Singular forms retain all N-r radical factors, and odd as well as even ranks are included: the factor (-|L|)^r keeps its sign. This calculation makes no Fourier-orbit identification, rank-parity, global-phase or entropy assertion, and does not complete a parent atom. The congruence's unresolved REG obligation remains tracked by issue #16473; this exposition does not settle it."))));

    private static Formula ApplicationDefinitions()
    {
        var x = F.Id("X");
        var scalar = F.Id("x");
        return Seq(
            Typed(HermitianSymbol, Arrow(Vector, F.Id("L"))), Comma, Sp,
            HermitianValue(x), Sp, Eq, Sp,
            Call("transpose", x), Sp, Cdot, Sp, F.Id("B"), Sp, Cdot, Sp, Call("sigma", x),
            Sp, InMacro, Sp, F.Id("L"), Qquad,
            Typed(Nu, Arrow(F.Id("K"), F.Id("L"))), Comma, Sp,
            NormValue(scalar), Sp, Eq, Sp, Call("AlgebraNorm", F.Id("L"), scalar),
            Sp, Eq, Sp, scalar, Sp, Cdot, Sp, Call("sigma", scalar));
    }

    private static Formula CharacterDefinition() => Seq(
        Typed(Psi, Arrow(F.Id("L"), ComplexField)), Comma, Sp,
        CharacterValue(F.Id("a")), Sp, Eq, Sp, TraceSign(F.Id("a")));

    private static Formula DiagonalNormSum() => Seq(
        HermitianValue(Seq(F.Id("T"), Sp, Cdot, Sp, F.Id("Y"))), Sp, Eq, Sp,
        SumOver(Seq(Typed(F.Id("i"), Call("Fin", F.Id("N"))), Sp, Mid, Sp,
            Call("val", F.Id("i")), Sp, Lt, Sp, F.Id("r")),
            NormValue(Call("Y", F.Id("i")))));

    private static Formula ScalarNormSum() => Seq(
        SumOver(Typed(F.Id("x"), F.Id("K")), CharacterValue(NormValue(F.Id("x")))),
        Sp, Eq, Sp, D(1), Sp, Plus, Sp,
        Seq(Open, Typed(Card(F.Id("L")), ComplexField), Sp, Plus, Sp, D(1), Close),
        Sp, Cdot, Sp,
        SumOver(Seq(Typed(F.Id("a"), F.Id("L")), Sp, Mid, Sp,
            F.Id("a"), Sp, Neq, Sp, D(0)), CharacterValue(F.Id("a"))),
        Sp, Eq, Sp, Minus, Typed(Card(F.Id("L")), ComplexField));

    private static Formula SignedTraceSum() => Seq(
        SumOver(Typed(F.Id("X"), Vector), TraceSign(HermitianValue(F.Id("X")))),
        Sp, Eq, Sp,
        Typed(Card(F.Id("K")), ComplexField), Caret,
        Grp(F.Id("N"), Sp, Minus, Sp, Call("rank", F.Id("B"))), Sp, Cdot, Sp,
        Seq(Open, Minus, Typed(Card(F.Id("L")), ComplexField), Close), Caret,
        Grp(Call("rank", F.Id("B"))));

    private static Formula TraceSign(Formula value) => Seq(
        Typed(Seq(Minus, D(1)), ComplexField), Caret,
        Grp(Call("val", Call("AlgebraTrace", Call("ZMod", D(2)), F.Id("L"), value))));
    private static Formula HermitianSymbol => Seq(F.Id("H"), Underscore, Grp(F.Id("B")));
    private static Formula HermitianValue(Formula value) => Seq(HermitianSymbol, Open, value, Close);
    private static Formula NormValue(Formula value) => Seq(Nu, Open, value, Close);
    private static Formula CharacterValue(Formula value) => Seq(Psi, Open, value, Close);
    private static Formula ComplexField => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Vector => Arrow(Call("Fin", F.Id("N")), F.Id("K"));
    private static Formula Arrow(Formula domain, Formula codomain) => Seq(Open, domain, Sp, To, Sp, codomain, Close);
    private static Formula Card(Formula type) => Seq(Lvert, Sp, type, Rvert);
    private static Formula SumOver(Formula index, Formula value) => Seq(Sum, Underscore, Grp(index), Sp, value);

    private static Formula Statement()
    {
        var k = F.Id("K");
        var sigma = F.Id("sigma");
        var n = F.Id("N");
        var b = F.Id("B");
        var t = F.Id("T");
        var i = F.Id("i");
        var matrix = Call("Matrix", Call("Fin", n), Call("Fin", n), k);
        var hypotheses = Seq(Call("Involutive", sigma), Sp, Land, Sp,
            sigma, Sp, Neq, Sp, Call("RingEquivRefl", k), Sp, Land, Sp,
            Call("transpose", Call("map", b, sigma)), Sp, Eq, Sp, b);
        var diagonal = Call("diagonal", Seq(Typed(i, Call("Fin", n)), Sp, Mapsto, Sp,
            Call("ite", Seq(Call("val", i), Sp, Lt, Sp, Call("rank", b)), D(1), D(0))));
        var conclusion = Some(t, matrix, Seq(Call("IsUnit", t), Sp, Land, Sp,
            Call("transpose", t), Sp, Cdot, Sp, b, Sp, Cdot, Sp, Call("map", t, sigma),
            Sp, Eq, Sp, diagonal));
        return All(k, Call("Type"), Seq(OpenBracket, Call("Field", k), CloseBracket, Sp,
            OpenBracket, Call("Finite", k), CloseBracket, Sp,
            All(sigma, Call("RingEquiv", k, k), All(n, Seq(Mathbb, Grp(F.Id("N"))),
                All(b, matrix, Seq(Open, hypotheses, Close, Sp, Rightarrow, Sp, conclusion))))));
    }

    private static Formula Typed(Formula name, Formula type) => Seq(Open, name, Sp, Colon, Sp, type, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
}
