using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OriginalOcticSplitDeterminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The split determinant of the original octic window is irreducible over every characteristic-zero splitting field.",
        H("The labeled octic window"),
        Blocks(
            Paragraph(Text("Let alpha be an element of a field D with alpha to the eighth power equal to two. Let sigma_0 through sigma_7 be embeddings into a characteristic-zero field k. Fix a primitive eighth root zeta in k and preserve the labels sigma_i(alpha)=sigma_0(alpha) zeta^i. The four columns are the images of 1, alpha, alpha^3 and alpha^4 in that order. The polynomial is the determinant of the eight columns [B | diag(q) B], with rows labeled zero through seven. In the formulas, fourSets is the set of all four-element subsets of Fin 8, and RingHomFamily(Fin 8,D,k) means a family of eight unital ring homomorphisms from D to k. The exponent i is the representative zero through seven of its original label.")),
            Describe.Lean(DescribeId.Create("normalized-coefficient-count"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.coefficient_zero_count"),
                H("The exact normalized coefficient count"),
                StatementSource.FromAuthor(CountStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There are seventy four-element label sets. The normalized integer coefficient function vanishes at eighteen of them. Its other values belong to the set consisting of plus or minus one, two and four."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("original-determinant-structure"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_structure"),
                H("Structure of the actual determinant"),
                StatementSource.FromAuthor(StructureStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This statement derives homogeneity of degree four, degree at most one in each variable and exactly eighteen zero squarefree quartic coefficients from the root relations themselves.")),
                    Paragraph(Text("Put s=zeta+zeta^3, so s squared equals minus two. If U is the matrix of the first four rows of B, the last four rows are R U, where the rows of R are (-1,-s,2,s), (-s,1,s,0), (0,-s,1,s) and (-s,2,s,-1). The square of det(U) is 128. Block elimination expresses the eight-by-eight determinant as 128 times the determinant whose entry (i,j) is R(i,j)(q_(4+i)-q_j). Expanding this four-by-four determinant gives precisely the normalized integer coefficients counted above. No row permutation changes the original labels."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-determinant-irreducibility"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible"),
                H("Irreducibility with the original embeddings"),
                StatementSource.FromAuthor(IrreducibilityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Applying each embedding to alpha^8=2 identifies its row with the root matrix used in the structure theorem. The homogeneous multiaffine quartic obstruction applies because eighteen is less than twenty. Thus the actual determinant is irreducible over k. The statement quantifies every characteristic-zero field containing these embeddings and the primitive root, so it also applies after further field extension.")),
                    Paragraph(Text("The original field element, its four powers and all eight embedding labels remain explicit. This determinant statement does not assert a classification of rational windows with equal quotient support."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Application to the Auric 41.13 window"), Blocks(
                Paragraph(Text("For the Auric specialization, take the designated positive real root alpha = 2^(1/8), let D = Q(alpha) inside C, choose zeta = exp(pi i/4), and put K = D(zeta). Fix any Q-algebra homomorphism lambda: K -> k into an algebraically closed characteristic-zero field k with its Q-algebra structure. For each label i, let sigma_i: D -> K be the Q-algebra embedding sending alpha to alpha zeta^i, and put tau_i = lambda composed with sigma_i. Let X be the Q-span of 1, alpha, alpha^3 and alpha^4. The actual quotient set QX consists of u/v with u and v in X and v nonzero; it contains 0 by taking u = 0 and v = 1. Its image S consists of embed(x) = (tau_i(x)) for x in QX. The original labels are ordered 0 through 7, with Fin 8 and ZMod 8 identified by their representatives. Every row and column index below starts at zero.")),
                Paragraph(Text("Let B be the exact eight-by-four matrix whose row i is the four tau_i-values of 1, alpha, alpha^3 and alpha^4, and let P(q) be the determinant of [B | diag(q) B] with those original row labels and the displayed column order. Under the order-preserving identification of Fin 8 and ZMod 8, P is exactly splitDeterminant(B), with only the corresponding renaming of polynomial variables and no determinant sign or scalar change. The forward inclusion is the actual-kernel calculation: for rational coordinates a,b with the denominator element of X nonzero, the vector (-a,b), mapped into k, is a nonzero kernel vector of the evaluated split matrix at q = embed(u/v). Therefore P vanishes on every point of S, including zero.")),
                Paragraph(Text("The reverse direction first transfers rational parameters to arbitrary coefficients in k. Clearing the finitely many linear denominators gives a polynomial identity in two blocks of coefficient variables; the rational coefficient points are Zariski dense because k has characteristic zero. Hence vanishing for every rational numerator and every nonzero rational denominator transfers to every k-valued numerator and denominator for which all eight transported denominators are nonzero.")),
                Paragraph(Text("On the open chart where the determinant vanishes and the cofactor product is nonzero, let M(q) be the evaluated eight-by-eight split matrix and take column indexed 7 of adjugate(M(q)), namely its eighth column. The negatives of its entries indexed 0 through 3 define U, and its entries indexed 4 through 7 define V; set H(q) = product over i of (B times V(q))_i. The identity M times adjugate(M) = det(M) times the identity gives q_i = (B times U(q))_i / (B times V(q))_i whenever P(q) = 0 and H(q) is nonzero. This is the inverse chart used by the rational-parameter transfer.")),
                Paragraph(Text("The chart is nonempty at the square point qstar_i = tau_i(alpha)^2. The determinant is zero because columns indexed 2 and 5, the third and sixth columns, coincide there. Put c = adjugate(M(qstar))_(5,7); this is the signed minor obtained by deleting row indexed 7 and column indexed 5 from M(qstar). The remaining seven-by-seven matrix is a column permutation of a Vandermonde matrix on the transported roots with labels 0 through 6. Their distinctness follows from the original labels and the primitive-root relation, so the pinned Mathlib criterion Matrix.det_vandermonde_ne_zero_iff gives c nonzero. The adjugate identities give (B times V(qstar))_i = c tau_i(alpha); each transported root is nonzero, and hence H(qstar) is nonzero.")),
                Paragraph(Text("The existing irreducibility result D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible makes this same P prime over k. For every polynomial f in the eight variables with arbitrary coefficients in k, vanishing on S transfers to the nonempty cofactor chart. Thus H f vanishes on the full zero locus of P. The pinned Nullstellensatz identity MvPolynomial.IsPrime.vanishingIdeal_zeroLocus gives P dividing H f. Since P(qstar) = 0 and H(qstar) is nonzero, P does not divide H; primality gives P dividing f. Together with the forward inclusion, f vanishes on S if and only if P divides f, so the vanishing ideal of S is exactly the principal ideal (P). For the affine Zariski topology induced from the prime spectrum by the point-evaluation map, closed sets are precisely polynomial ideal zero loci. Consequently the affine Zariski closure of S is V(P).")),
                Paragraph(Text("The reused ingredients are the irreducibility and determinant statements above together with the pinned Mathlib suppliers Matrix.mul_adjugate, Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_vandermonde_ne_zero_iff, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus and Ideal.mem_span_singleton. This application uses one fixed lambda throughout and describes its parameter correspondence and the nonzero-chart boundary. It does not use a rank/Jacobian route, assert the subsequent proportionality statement, or complete the general window classification or trace-dual analysis.")))))));
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open,
            Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray()), Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Labels() => Call("Fin", D(8));
    private static Formula P() => Call("splitDeterminant",
        Call("originalWindowMatrix", F.Id("a"), F.Id("z")));
    private static Formula ZeroCount(Formula f) => Call("card", Seq(OpenBrace, F.Id("I"),
        InMacro, Sp, F.Id("fourSets"), Mid, Call("coeff", f, Call("squareExponent", F.Id("I"))), Eq, D(0), CloseBrace));
    private static Formula CountStatement() => Disp(Seq(Call("card", Seq(OpenBrace, F.Id("I"),
        InMacro, Sp, F.Id("fourSets"), Mid, Call("integerCoefficient", F.Id("I")), Eq, D(0), CloseBrace)), Eq, D(1,8)));
    private static Formula FieldAssumptions() => Seq(Call("Field", F.Id("k")), Land, Call("CharZero", F.Id("k")));
    private static Formula StructureStatement() => Disp(Seq(Forall, Sp, F.Id("k"), Comma, Sp,
        FieldAssumptions(), Implies, All("a", F.Id("k"), All("z", F.Id("k"), Seq(
            F.Id("a"), Caret, Grp(D(8)), Eq, D(2), Land, Call("IsPrimitiveRoot", F.Id("z"), D(8)),
            Implies, Call("IsHomogeneous", P(), D(4)), Land,
            Open, All("i", Labels(), Seq(Call("degreeOf", F.Id("i"), P()), Le, D(1))), Close,
            Land, ZeroCount(P()), Eq, D(1,8))))));
    private static Formula IrreducibilityStatement() => Disp(Seq(Forall, Sp, F.Id("k"), Comma, Sp,
        Forall, Sp, F.Id("D"), Comma, Sp, FieldAssumptions(), Land, Call("Field", F.Id("D")), Implies,
        All("alpha", F.Id("D"), All("sigma", Call("RingHomFamily", Labels(), F.Id("D"), F.Id("k")),
        All("z", F.Id("k"), Seq(F.Id("alpha"), Caret, Grp(D(8)), Eq, D(2), Land,
            Call("IsPrimitiveRoot", F.Id("z"), D(8)), Land,
            Open, All("i", Labels(), Seq(Call("sigma", F.Id("i"), F.Id("alpha")), Eq,
                Call("sigma", D(0), F.Id("alpha")), Cdot, Sp, F.Id("z"), Caret, Grp(F.Id("i")))), Close,
            Implies, Call("Irreducible", Call("splitDeterminant",
                Call("originalFieldWindowMatrix", F.Id("alpha"), F.Id("sigma"))))))))));
}
