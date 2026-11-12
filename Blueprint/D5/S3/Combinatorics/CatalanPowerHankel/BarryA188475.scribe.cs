using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CatalanPowerHankel;

internal sealed class BarryA188475Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CatalanPowerHankel/BarryA188475.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/barry2011a188475");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Barry A188475 shifted Hankel conjecture for the literal Catalan recurrence.",
        H("Barry's Original Shifted Hankel Determinant"),
        Blocks(
            Paragraph(Text("Barry's original OEIS A188475 assertion is ‘Hankel transform of "
                + "A137398(n+1) (conjecture)’. A137398 originally had offset zero and later "
                + "changed to offset one. In the current numbering its recurrence defines "
                + "q(1)=0, q(2)=1, q(3)=2. The original shifted matrix therefore has entries "
                + "q(i+j+2), with i and j from zero through n. No tabulated prefix defines q.")),
            Describe.Lean(DescribeId.Create("barry-a188475-source-recurrence"),
                DeclarationHandle.Create(Prefix + "q"), H("The literal source recurrence"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Equal(Q(D(0)), D(0)), Comma, Sp, Equal(Q(D(1)), D(0)), Comma, Sp,
                        Equal(Q(D(2)), D(1)), Comma, Sp, Equal(Q(D(3)), D(2))),
                    All("n", Naturals(), Equal(Q(Add(N(), D(3))), Add(
                        Add(Mul(D(2), Q(Add(N(), D(2)))), Mul(D(2), Q(Add(N(), D(1))))),
                        SigmaRange(N(),
                            Mul(Call("catalan", Add(K(), D(1))),
                                Q(Subtract(Add(N(), D(1)), K())))))))
                ]))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("All values lie in ℚ. The sum is over k in Finset.range n "
                    + "and is empty at n=0; hence the recursive clause also gives q(3)=2. "
                    + "The value at zero is auxiliary. For n≥1 the substitution r=n+3 and "
                    + "the change of summation index k↦k+1 give exactly the source's "
                    + "positive-index Catalan recurrence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("barry-a188475-shifted-matrix"),
                DeclarationHandle.Create(Prefix + "hankel"), H("The exact shifted matrix"),
                StatementSource.FromAuthor(Disp(All("N", Naturals(),
                    All("i", Call("Fin", F.Id("N")), All("j", Call("Fin", F.Id("N")),
                        Equal(Call("hankel", F.Id("N"), F.Id("i"), F.Id("j")),
                            Q(Add(Add(F.Id("i"), F.Id("j")), D(2))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("hankel(N) is a rational N by N matrix. In the theorem "
                    + "N=n+1, so its row and column indices are precisely 0,...,n. "
                    + "Every source index is at least two."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("barry-a188475-all-index-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The complete original conjecture"),
                StatementSource.FromAuthor(Disp(All("n", Naturals(), Seq(
                    Equal(Det(), Add(D(1), Mul(D(2), Sigma("k", D(0), N(), Pow(K(), D(2)))))),
                    Sp, Land, Sp,
                    Equal(Det(), new Formula.Fraction(Add(Add(Add(
                        Mul(D(2), Pow(N(), D(3))), Mul(D(3), Pow(N(), D(2)))), N()), D(3)), D(3))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let C be the rational formal Catalan series, T=C², "
                        + "F=Σq(r)Xʳ and M=1+2F. The literal recurrence proves "
                        + "F(1−2X−2X²−X²T)=X². The Catalan equation proves "
                        + "T(1−2X−X²T)=1. Together they give M(1−2X²T)=1.")),
                    Paragraph(Text("Use the monic family P₀=1, P₁=X and "
                        + "Pⱼ₊₂=(X−2)Pⱼ₊₁−βⱼPⱼ, where β₀=2 and βⱼ₊₁=1. "
                        + "The reversed-polynomial generating errors vanish below degree 2j "
                        + "and have leading coefficient two for j≥1. Coefficient extraction "
                        + "therefore gives all-index orthogonality with norms 1,2,2,... .")),
                    Paragraph(Text("The monic coefficient matrix A has determinant one. "
                        + "Its finite Gram congruence is AᵀGA=diag(1,2,...,2). The adjugate "
                        + "product identity gives adj(G)=A adj(diag(1,2,...,2)) Aᵀ. "
                        + "The recurrence yields Pⱼ₊₁(0)=2(−1)ʲj, whose square is 4j². "
                        + "Thus the (0,0) cofactor equals 2ᴺ(1+2Σⱼ₌₀ᴺ⁻¹j²). "
                        + "Deleting row and column zero from G also gives twice hankel(N) "
                        + "entry by entry. Cancel the nonzero rational power 2ᴺ and set "
                        + "N=n+1. Induction evaluates the sum of squares to the cubic. "
                        + "The proof includes n=0 and assumes no moment representation "
                        + "or conditional identity for q."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a188475-original-shifted-hankel"), ResolutionKind.Proved))
        ), [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge"))]));

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Q(Formula k) => Call("q", k);
    private static Formula Det() => Call("det", Call("hankel", Add(N(), D(1))));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula SigmaRange(Formula bound, Formula term) =>
        Seq(Sum, Underscore, Grp(K(), Sp, InMacro, Sp, Call("range", bound)), Sp, term);
    private static Formula Sigma(string name, Formula lower, Formula upper, Formula term) =>
        Seq(Sum, Underscore, Grp(Equal(F.Id(name), lower)), Caret, Grp(upper), Sp, term);
}
