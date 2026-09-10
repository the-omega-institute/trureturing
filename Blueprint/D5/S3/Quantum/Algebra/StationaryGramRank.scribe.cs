using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class StationaryGramRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite occupation recurrence bounds the nullity of a normalized positive semidefinite matrix.",
        H("Stationary Gram Rank"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stationary-gram-rank-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/StationaryGramRank.stationary_gram_rank_lower_bound"),
                H("The finite-box rank bound"),
                StatementSource.FromAuthor(RankFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let sigma be any finite type and let a map sigma to the natural numbers. " +
                        "The set TailBox(a) consists of functions r with r(i) in Fin(a(i)+1). " +
                        "Its zero element has every coordinate zero. Let B be a complex matrix " +
                        "indexed by this box. Assume B is positive semidefinite and B(0,0)=1. " +
                        "For each pair of nonzero box elements r and s, assume B(r,s) is the sum " +
                        "over i of B(r-e(i),s-e(i)), including a summand only when both r(i) " +
                        "and s(i) are positive. Each coordinate of r-e(i) is the natural " +
                        "truncated difference r(j) minus one if j=i, and r(j) otherwise. " +
                        "These lowerings remain in the same box.")),
                    Paragraph(Text(
                        "Then rank B is at least the product of a(i)+1 minus the finite " +
                        "supremum of a(i). The subtraction in this bound is natural subtraction. " +
                        "The supremum is zero and the product is one for an empty sigma. " +
                        "No positivity of the capacities or of individual matrix entries is " +
                        "required. In particular, the assertion includes all-zero capacities " +
                        "and supremum zero or one. The recurrence is required only when both " +
                        "indices are nonzero.")),
                    Paragraph(Text(
                        "Define T(i) on coordinate basis vectors by lowering the i-th coordinate " +
                        "when that coordinate is positive, and sending the vector to zero " +
                        "otherwise. If u(0)=0, the recurrence gives u*Bu equal to the sum of " +
                        "(T(i)u)*B(T(i)u). Terms with a zero row or column vanish because " +
                        "u(0)=0. When u belongs to the kernel of B, this sum is zero. " +
                        "Positive semidefiniteness makes every summand nonnegative, so each " +
                        "is zero and every T(i)u also belongs to the kernel.")),
                    Paragraph(Text(
                        "Send the coordinate basis vector at r to the monomial x^r divided " +
                        "by the product of the factorials r(i)!. This is a linear isomorphism " +
                        "onto the polynomials supported on exponents bounded by a. " +
                        "The nonzero factorial factors rescale the monomial basis. " +
                        "The identity n!=n(n-1)! shows that this map J satisfies " +
                        "partial(i)(J(u))=J(T(i)u), and its constant coefficient is u(0).")),
                    Paragraph(Text(
                        "Let L be the image under J of the kernel of B. If a constant c " +
                        "belongs to L, injectivity of J identifies its inverse image with " +
                        "c times the coordinate vector at zero. The zero row of the kernel " +
                        "equation and B(0,0)=1 then give c=0. The conditional lowering " +
                        "property gives closure of L under partial derivatives of members " +
                        "with zero constant coefficient. Its support is rectangular, so the " +
                        "rectangular polynomial nullity bound gives dim L at most the " +
                        "finite supremum of a. Injectivity of J preserves the kernel " +
                        "dimension. Finally, the function space on TailBox(a) has dimension " +
                        "equal to the product of a(i)+1, and rank-nullity gives the claimed bound."))),
                DescribeRole.Theorem))));

    private static Formula RankFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula a = F.Id("a");
        Formula matrix = F.Id("B");
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula box = Call("TailBox", a);
        Formula index = Seq(i, Sp, InMacro, Sp, sigma);
        Formula positiveCoordinates = Seq(
            D(0), Sp, Lt, Sp, Call("val", Call("r", i)), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, Call("val", Call("s", i)));
        Formula Lower(Formula row) => Seq(
            LambdaLower, Sp, j, Colon, Sp, sigma, Comma, Sp,
            Call("FinMk", Call("NatSub", Call("val", Seq(row, Open, j, Close)),
                Call("if", Seq(j, Sp, Eq, Sp, i), D(1), D(0)))));
        Formula recurrence = Seq(
            Forall, Sp, r, Comma, Sp, s, Colon, Sp, box, Comma, Sp,
            r, Sp, Neq, Sp, D(0), Sp, Implies, Sp,
            s, Sp, Neq, Sp, D(0), Sp, Implies, Esc,
            Call("B", r, s), Sp, Eq, Sp,
            Sum, Underscore, Grp(index), Sp,
            Call("if", positiveCoordinates,
                Call("B", Lower(r), Lower(s)), D(0)));
        Formula cardinality = Seq(
            Prod, Underscore, Grp(index), Sp,
            Open, Call("a", i), Sp, Plus, Sp, D(1), Close);

        return Disp(Seq(
            Forall, Sp, sigma, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("Fintype", sigma), Comma, Esc,
            Forall, Sp, a, Colon, Sp, sigma, Sp, To, Sp, F.Id("Nat"), Comma, Esc,
            Forall, Sp, matrix, Colon, Sp, Call("Matrix", box, box, F.Id("Complex")), Comma, Esc,
            Call("PosSemidef", matrix), Sp, Implies, Esc,
            Call("B", D(0), D(0)), Sp, Eq, Sp, D(1), Sp, Implies, Esc,
            Open, recurrence, Close, Sp, Implies, Esc,
            Call("NatSub", cardinality, Call("FinsetSup", Call("univ", sigma), a)),
            Sp, Leq, Sp, Call("rank", matrix), Dot));
    }
}
