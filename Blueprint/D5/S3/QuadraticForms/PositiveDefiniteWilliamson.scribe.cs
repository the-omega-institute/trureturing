using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class PositiveDefiniteWilliamsonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Oriented skew paired-plane induction constructs one positive Williamson congruence for any finite set of modes, including the empty set.",
        H("Finite-Mode Positive Williamson Form"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skew-paired-basis-induction"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/PositiveDefiniteWilliamson.skew_paired_basis_induction"),
                H("An actual oriented paired orthonormal frame"),
                StatementSource.FromAuthor(PairingFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/kaplanski2026williamson")),
                Blocks(
                    Paragraph(Text("For every even-dimensional finite real inner product space E and every real linear skew operator a, there are a finite index set K, a complete orthonormal basis indexed by K plus K, and nonnegative frequencies nu. The action is a(p_k)=-nu_k q_k and a(q_k)=nu_k p_k. Zero dimension and the zero operator are included.")),
                    Paragraph(Text("The construction extracts an invariant orthonormal plane from a negative Rayleigh eigenvalue of a squared, or an arbitrary orthonormal pair when a is zero. Skew adjointness makes the plane's orthogonal complement invariant. Strong induction and orthonormal gluing produce the whole frame, without assuming a paired-basis certificate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-definite-williamson"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/PositiveDefiniteWilliamson.positive_definite_williamson"),
                H("The same symplectic matrix supplies the energy congruence"),
                StatementSource.FromAuthor(WilliamsonFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/kaplanski2026williamson")),
                Blocks(
                    Paragraph(Text("For any finite mode set L and real positive-definite matrix M on L plus L, one actual matrix S is symplectic and satisfies S-transpose J S=J and S-transpose M S=diag(nu,nu), with every frequency strictly positive. The theorem has no nonempty-mode hypothesis.")),
                    Paragraph(Text("Set R=sqrt(M) and apply the paired-frame induction to A=R J R. The resulting orthogonal O puts A into the block form with upper-right diag(nu) and lower-left -diag(nu). Invertibility of A and nonzero basis vectors force positive frequencies. With E=[[0,sqrt(D)],[sqrt(D),0]], the single S=R-inverse O E gives both symplectic relations and the repeated diagonal energy.")),
                    Paragraph(Text("This is an attributed port of PK's selected QIQT-H source. Mathlib supplies the Rayleigh, adjoint-complement, basis, coordinate, functional-calculus and matrix inverse interfaces.")),
                    Paragraph(Text("Mathlib J=[[0,-I],[I,0]] is the negative of physical J+. The same S preserves both signs. The result supplies only a supporting matrix step for original theorem 2.4 within consolidated theorem 2.3; the observation-compatible split, metaplectic implementation, domains, completed tensor factorization and Gibbs trace identities require separate results."))),
                DescribeRole.Theorem))));

    private static Formula PairingFormula() => Disp(Seq(
        Forall, Sp, F.Id("E"), Comma, Sp, F.Id("a"), Comma, Sp,
        Call("FiniteRealInnerProductSpace", F.Id("E")), Sp, Land, Sp,
        Call("Even", Call("finrank", F.Id("E"))), Sp, Land, Sp,
        Call("Skew", F.Id("a")), Sp, Rightarrow, Sp,
        Exists, Sp, F.Id("K"), Comma, Sp, F.Id("b"), Comma, Sp, F.Id("nu"), Comma, Sp,
        Call("Finite", F.Id("K")), Sp, Land, Sp,
        Call("OrthonormalBasis", Call("Sum", F.Id("K"), F.Id("K")), F.Id("b")), Sp, Land, Sp,
        Call("Nonnegative", F.Id("nu")), Sp, Land, Sp,
        Call("PairedAction", F.Id("a"), F.Id("b"), F.Id("nu"))));

    private static Formula WilliamsonFormula() => Disp(Seq(
        Forall, Sp, F.Id("L"), Comma, Sp, F.Id("M"), Comma, Sp,
        Call("Finite", F.Id("L")), Sp, Land, Sp,
        Call("PosDef", F.Id("M")), Sp, Rightarrow, Sp,
        Exists, Sp, F.Id("S"), Comma, Sp, F.Id("nu"), Comma, Sp,
        Call("Symplectic", F.Id("S")), Sp, Land, Sp,
        Call("Positive", F.Id("nu")), Sp, Land, Sp,
        Equal(Multiply(Multiply(Call("transpose", F.Id("S")), F.Id("J")), F.Id("S")), F.Id("J")), Sp, Land, Sp,
        Equal(Multiply(Multiply(Call("transpose", F.Id("S")), F.Id("M")), F.Id("S")),
            Call("diag", F.Id("nu"), F.Id("nu")))));
}
