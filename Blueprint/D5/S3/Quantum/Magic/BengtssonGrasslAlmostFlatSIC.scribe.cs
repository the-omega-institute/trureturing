using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class BengtssonGrasslAlmostFlatSICDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/bengtssongrassl2025almostflat");
    private static readonly Formula d = F.Id("d"), v = F.Id("v"), j = F.Id("j"), r = F.Id("r"), a = F.Id("a"), b = F.Id("b"), k = F.Id("k"), c = F.Id("C");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every almost flat Weyl-Heisenberg SIC fiducial in odd dimension satisfies the X-overlap equation. Finite character orthogonality supplies a diagonal quartic contraction; conjugate reflection and midpoint reindexing reduce its total to a saturated phase bound.",
        H("The almost flat SIC X-overlap equation"), Blocks(
            Entry("IsAlmostFlat", "The almost flat ansatz", Dim(All("v", Vec(d), Iff(Flat(),
                And(Eq(At(v, D(0)), Mul(F.Id("i"), Root(Add(Root(Add(d, D(1))), D(2))))),
                    All("j", Z(d), Imp(Ne(j, D(0)), And(Eq(Norm(At(v, j)), D(1)),
                        Eq(At(v, Negate(j)), Negate(Conj(At(v, j))))))))))),
                "The zeroth coordinate is i times the positive square root of sqrt(d+1)+2. Every other coordinate has modulus one and negative conjugate reflection. No existence assertion is included.", DescribeRole.Definition),
            Entry("almostFlatNorm", "The normalization denominator", All("d", Field("N"),
                Eq(Call("almostFlatNorm", d), Add(Add(d, D(1)), Root(Add(d, D(1)))))),
                "This real number is d+1+sqrt(d+1), equal to the Hermitian squared norm of an almost flat vector.", DescribeRole.Definition),
            Entry("shift_pow_mulVec", "The action of every shift power", Dim(All("n", Field("N"), All("v", Vec(d), All("r", Z(d),
                Eq(At(Mul(Pow(Call("shiftMatrix", d), F.Id("n")), v), r), At(v, Sub(r, F.Id("n")))))))),
                "The circulant convention gives (X to the power n times v) at r equal to v at r-n. Exponents on the left are natural numbers and indices on the right are residues."),
            Entry("displacement_overlap_sum", "Weyl overlaps in coordinates", WithV(All("a", Z(d), All("b", Z(d),
                Eq(Overlap(a, b), Sum("r", Z(d), Mul(Mul(Conj(At(v, Add(r, a))), At(v, r)), Chi(Mul(b, r)))))))),
                "The displacement is X to the power a times Z to the power b. The standard positive additive character is denoted chi. Shifting the summation variable removes the translation from the clock factor."),
            Entry("spectral_autocorrelation", "Character orthogonality and autocorrelation", Spectral(),
                "Expand a Fourier sum times its conjugate and sum over the character index. Orthogonality retains exactly the terms r=t+j. This identity holds for every complex function on the cyclic index group."),
            Entry("diagonal_quartic", "The diagonal quartic contraction", WithV(All("K", Field("R"), Imp(NormLaw(F.Id("K")),
                All("j", Z(d), Eq(G(j), If(Eq(j, D(0)), Mul(D(2), F.Id("K")), D(0))))))),
                "Apply spectral autocorrelation to f(r)=conjugate(v(r+j)) v(r). The autocorrelation is the conjugate of the displayed quartic sum. The SIC spectral squares are constant away from the identity, so only j=0 survives, with value 2K."),
            Entry("overlap_sum", "The explicit negative even-shift overlap", WithV(All("j", Z(d), Eq(XOverlap(j), A(j)))),
                "The negative even shift X to the power -2j uses the least nonnegative representative of its residue. Its matrix overlap is exactly the sum of conjugate(v(r)) v(r+2j)."),
            Entry("conjugate_reflection", "Reflection at every coordinate", WithV(Imp(Flat(), All("r", Z(d),
                Eq(Conj(At(v, r)), Negate(At(v, Negate(r))))))),
                "The ansatz reflection extends to zero because the distinguished coordinate is purely imaginary."),
            Entry("coordinate_norm_sq", "The squared coordinate norms", WithV(Imp(Flat(), All("r", Z(d),
                Eq(Pow(Norm(At(v, r)), D(2)), Add(D(1), If(Eq(r, D(0)), C(), D(0))))))),
                "The squared norm is sqrt(d+1)+2 at zero and one elsewhere."),
            Entry("squared_norm", "The actual squared norm", WithV(Imp(Flat(), Eq(Call("inner", v, v), Call("almostFlatNorm", d)))),
                "Summing the coordinate squared norms gives the exact normalization denominator."),
            Entry("sic_overlap_squares", "Removing the normalization factor", WithV(Imp(Flat(), Imp(Sic(), NormLaw(Pow(C(), D(2)))))),
                "Write s=sqrt(d+1) and C=s+1. The denominator L=sC, so unnormalized nonidentity overlap moduli are C. The identity overlap is L; its square is C squared times d+1."),
            Entry("overlap_convolution", "Autocorrelation as negative convolution", WithV(Imp(Flat(), All("j", Z(d),
                Eq(A(j), Negate(B(j)))))),
                "Substitute r by -r and use conjugate reflection. This explains the negative sign in the midpoint contraction."),
            Entry("midpoint_contraction", "Summing over the midpoint", WithV(Imp(Flat(),
                Eq(Sum("j", Z(d), G(j)), Negate(Sum("k", Z(d), Mul(Pow(Conj(At(v, k)), D(2)), A(k))))))),
                "For each fixed r, replace j by k=r+j, interchange the two finite sums and use the negative convolution identity."),
            Entry("phase_saturation", "A saturated aggregate phase bound", Saturation(),
                "For a finite index set S, each z has modulus one and each A has modulus C. Expanding the sum of norm squares of A-C z squared gives zero when the aggregate conjugate phase sum is C times the cardinality. Nonnegativity forces every error to vanish."),
            Describe.Lean(DescribeId.Create("bengtsson-grassl-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The X-overlap equation in every odd dimension"), StatementSource.FromAuthor(Disp(Result())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The diagonal quartic contraction sums to 2C squared. The zero term is conjugate(v(0)) squared times A(0)=-(s+2)L; removing it from the total -2C squared leaves C(d-1). Oddness makes multiplication by two invertible, so every remaining even shift is nonidentity and its overlap modulus is C. Phase saturation gives A(j)=C v(j) squared for every nonzero j. Dimension one has no such j. The theorem is conditional on a SIC fiducial and does not assert existence in any dimension. It does not address the converse, the even-dimensional formulas or alternative Weyl phase conventions."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bengtsson-grassl-2025-almost-flat-sic-conjecture"), ResolutionKind.Proved))), []));

    private static DocumentBlock Entry(string name, string title, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("bengtsson-grassl-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Field(string x) => Seq(Mathbb, Grp(F.Id(x)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Par(y));
    private static Formula All(string x, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Par(x), FormulaBinaryOperator.Multiply, Par(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(Par(x), FormulaBinaryOperator.Add, Par(y));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(Par(x), FormulaBinaryOperator.Subtract, Par(y));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(Par(x), y);
    private static Formula Negate(Formula x) => new Formula.Negate(Par(x));
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Conj(Formula x) => Call("conj", x);
    private static Formula Root(Formula x) => Call("sqrt", x);
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("ite", condition, yes, no);
    private static Formula Sum(string x, Formula type, Formula body) => Seq(F.Sum, Underscore, Grp(Seq(F.Id(x), Sp, Colon, Sp, type)), Sp, Par(body));
    private static Formula SumIn(string x, Formula set, Formula body) => Seq(F.Sum, Underscore, Grp(Seq(F.Id(x), Sp, InMacro, Sp, set)), Sp, Par(body));
    private static Formula Z(Formula n) => Call("ZMod", n);
    private static Formula Vec(Formula n) => Par(Seq(Z(n), Sp, To, Sp, Field("C")));
    private static Formula Dim(Formula body) => All("d", Field("N"), Imp(Ne(d, D(0)), body));
    private static Formula WithV(Formula body) => Dim(All("v", Vec(d), body));
    private static Formula Flat() => Call("IsAlmostFlat", d, v);
    private static Formula C() => Add(Root(Add(d, D(1))), D(1));
    private static Formula Sic() => Call("IsSICFiducial", d, Mul(Pow(Root(Call("almostFlatNorm", d)), Negate(D(1))), v));
    private static Formula Chi(Formula x) => Call("chi", x);
    private static Formula Overlap(Formula x, Formula y) => Call("inner", v, Mul(Call("displacement", d, x, y), v));
    private static Formula XOverlap(Formula x) => Call("inner", v, Mul(Pow(Call("shiftMatrix", d), Call("val", Negate(Mul(D(2), x)))), v));
    private static Formula A(Formula x) => Sum("r", Z(d), Mul(Conj(At(v, r)), At(v, Add(r, Mul(D(2), x)))));
    private static Formula B(Formula x) => Sum("r", Z(d), Mul(At(v, r), At(v, Sub(Mul(D(2), x), r))));
    private static Formula G(Formula x) => Sum("r", Z(d), Mul(Mul(Pow(Conj(At(v, Add(r, x))), D(2)), At(v, r)), At(v, Add(r, Mul(D(2), x)))));
    private static Formula NormLaw(Formula n) => All("a", Z(d), All("b", Z(d), Eq(Pow(Norm(Overlap(a, b)), D(2)),
        Mul(n, Add(D(1), If(And(Eq(a, D(0)), Eq(b, D(0))), d, D(0)))))));
    private static Formula Spectral()
    {
        Formula f = F.Id("f");
        Formula transform = Sum("r", Z(d), Mul(Chi(Mul(b, r)), At(f, r)));
        return Dim(All("f", Vec(d), All("j", Z(d), Eq(
            Sum("b", Z(d), Mul(Chi(Negate(Mul(b, j))), Mul(Conj(transform), transform))),
            Mul(d, Sum("r", Z(d), Mul(Conj(At(f, r)), At(f, Add(r, j)))))))));
    }
    private static Formula Saturation()
    {
        Formula t = F.Id("T"), s = F.Id("S"), z = F.Id("z"), aa = F.Id("A");
        Formula func = Par(Seq(t, Sp, To, Sp, Field("C")));
        Formula member = new Formula.Relation(k, FormulaRelationOperator.MemberOf, s);
        Formula phases = All("k", t, Imp(member, Eq(Norm(At(z, k)), D(1))));
        Formula moduli = All("k", t, Imp(member, Eq(Norm(At(aa, k)), c)));
        Formula total = Eq(SumIn("k", s, Mul(Pow(Conj(At(z, k)), D(2)), At(aa, k))), Mul(c, Call("card", s)));
        Formula conclusion = All("k", t, Imp(member, Eq(At(aa, k), Mul(c, Pow(At(z, k), D(2))))));
        return All("T", Call("Type"), Seq(OpenBracket, Call("DecidableEq", t), CloseBracket, Sp,
            All("S", Call("Finset", t), All("z", func, All("A", func, All("C", Field("R"),
                Imp(phases, Imp(moduli, Imp(total, conclusion)))))))));
    }
    private static Formula Result() => Dim(Imp(Call("Odd", d), All("v", Vec(d), Imp(Flat(), Imp(Sic(),
        All("j", Z(d), Imp(Ne(j, D(0)), Eq(XOverlap(j), Mul(C(), Pow(At(v, j), D(2)))))))))));
}
