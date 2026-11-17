using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class PartialTraceMutualInformationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/PartialTraceMutualInformation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial traces give density-state marginals, and independent product states have "
            + "zero quantum mutual information.",
        H("Partial Trace and Quantum Mutual Information"),
        Blocks(
            Paragraph(Text(
                "Application: the literal ordered-site Slater prefix marginal. "
                + "Fix natural numbers N, k and ell with k at most N and ell at most N. "
                + "Let V be a complex N by k matrix satisfying V adjoint V = I. "
                + "A Boolean word x on Fin N determines its occupied subset S(x), "
                + "the sites where x is true. Define psi(V,x) to be det(V restricted "
                + "to S(x) in increasing natural row order) when S(x) has size k, "
                + "and zero otherwise; the column order is unchanged. The Boolean "
                + "words are in bijection with all subsets of Fin N. Applying the "
                + "rectangular cauchyBinet formula as in CompoundMatrices and summing "
                + "the zero amplitudes gives sum over all x of conjugate(psi(V,x)) "
                + "times psi(V,x) = 1. Normalization is derived from V, rather than "
                + "assumed for a separately chosen state.")),
            Paragraph(Text(
                "Use Fin.appendEquiv ell (N - ell), followed by the equality "
                + "ell + (N - ell) = N, to concatenate a prefix word a on Fin ell "
                + "and a tail word b on Fin (N - ell) in the original site order. "
                + "Put psiSplit(a,b) = psi(V,ab) "
                + "and M((a,b),(a',b')) = psiSplit(a,b) conjugate(psiSplit(a',b')). "
                + "The literal matrix R(a,a') = sum over all tail words b of "
                + "psiSplit(a,b) conjugate(psiSplit(a',b)) is exactly "
                + "partialTraceRight(M). Matrix.posSemidef_vecMulVec_self_star "
                + "makes M positive semidefinite, and partialTraceRight_posSemidef "
                + "therefore makes R positive semidefinite. The diagonal sum, "
                + "reindexed by the same concatenation bijection, gives trace(R) = 1. "
                + "This constructs a density matrix on every Boolean prefix word, "
                + "including zero amplitudes, without any spectrum or correlation "
                + "assumption. The argument includes N = 0, k = 0, k = N and "
                + "ell = 0 or N.")),
            Paragraph(Text(
                "The ordered-prefix identity in CompoundMatrices has an actual "
                + "partial-trace consumer. For any complex ell by ell matrix U put "
                + "B = U directSum I_(N-ell), in the same literal site order. "
                + "The determinant-amplitude action gives psi(B V) = Gamma_N(B) "
                + "psi(V). After reindexing by Fin.appendEquiv, ordered-prefix "
                + "locality identifies Gamma_N(B) with Gamma_ell(U) tensor I on "
                + "all prefix and tail words. Hence the actual rank-one matrix "
                + "M_(B V) is (Gamma_ell(U) tensor I) M_V "
                + "(Gamma_ell(U) tensor I) adjoint. The existing "
                + "D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.trace_local_right "
                + "applied with its tail matrix equal to the identity therefore gives "
                + "R_(B V) = Gamma_ell(U) R_V Gamma_ell(U) adjoint. This derives "
                + "covariance from the literal minors and the literal partial trace; "
                + "covariance is not an input assumption. The identity itself holds "
                + "for arbitrary U and V, with no orthonormality premise.")),
            Paragraph(Text(
                "For a change of orthonormal one-particle basis, the exact hypothesis "
                + "is U adjoint U = I on Fin ell. The full occupation lift then "
                + "satisfies Gamma_ell(U) adjoint Gamma_ell(U) = I, so it belongs "
                + "to Matrix.unitaryGroup on every Boolean prefix word. Block "
                + "multiplication also gives B adjoint B = I, and therefore "
                + "(B V) adjoint (B V) = V adjoint V = I. This preserves the "
                + "actual normalized Slater construction. Taking N = ell + n "
                + "and then n = N - ell preserves arbitrary k at most N and "
                + "ell at most N, including N = 0, vacuum, full filling, empty "
                + "prefix and full prefix. This covariance application reuses "
                + "existing suppliers and introduces no new mathematical declaration.")),
            Paragraph(Text(
                "The actual kernel when the prefix compression is diagonal. Write "
                + "N = ell + n, X = V restricted to its first ell rows, and Y = V "
                + "restricted to the last n rows. Suppose only X X adjoint = diag(nu), "
                + "where nu is a real list indexed by every i in Fin ell. Then the "
                + "literal marginal above satisfies R(a,a') = delta(a,a') p(a), "
                + "where p(a) is the product over all i of nu(i) when a(i) is true "
                + "and 1 - nu(i) otherwise. This is an entry identity for the same "
                + "determinant-amplitude vector, rather than a state reconstructed "
                + "from its correlations. Orthonormality and the actual diagonal "
                + "compression are its only matrix hypotheses.")),
            Paragraph(Text(
                "Here is a coefficient derivation with exact parameter correspondence. "
                + "Let S and T be occupied prefix subsets of equal cardinality r, "
                + "and let X_S and X_T retain their increasing natural rows. Stack "
                + "X_S above Y, and X_T above the same Y. In cauchyBinet, weight "
                + "each of the first r rows by the polynomial variable t and each "
                + "tail row by one. Extracting the coefficient of t to the r "
                + "selects exactly the minors containing all r selected prefix "
                + "rows. Hence the actual sum over all tail subsets B of "
                + "det(V_(S union B)) conjugate(det(V_(T union B))) equals the "
                + "coefficient of t to the r in det(Y adjoint Y + "
                + "t X_T adjoint X_S). Each determinant is zero unless its row "
                + "count is k. The prefix and tail are joined by Fin.castAdd n "
                + "and Fin.natAdd ell, respectively, so these are exactly the "
                + "original natural-order minors. Finset.orderEmbOfFin_unique "
                + "identifies the increasing enumerations; no classical compound "
                + "order or unaccounted permutation sign enters this calculation.")),
            Paragraph(Text(
                "The original column orthonormality gives X adjoint X + "
                + "Y adjoint Y = I. Define E_(T,S) by its entry (i,j) being the "
                + "sum over q in Fin r of delta(i,T(q)) delta(j,S(q)), using the "
                + "increasing enumerations of S and T. Thus X_T adjoint X_S = "
                + "X adjoint E_(T,S) X. Matrix.det_one_add_mul_comm, applied "
                + "over the polynomial ring, changes the determinant above into "
                + "det(I - P + t E_(T,S) P), where P = X X adjoint. With "
                + "P = diag(nu), the variable rows are supported on T and the "
                + "variable columns on S. Reindex by T and its complement. "
                + "Matrix.det_fromBlocks_zero₂₁ and "
                + "Polynomial.coeff_det_X_add_C_card give the coefficient as "
                + "det((E_(T,S) diag(nu)) restricted to T by T) times the product "
                + "over i outside T of 1 - nu(i). If S = T the first matrix is "
                + "diagonal with entries nu(i). If S differs from T, equal "
                + "cardinality gives a site in T outside S, whose column is zero; "
                + "Matrix.det_eq_zero_of_column_eq_zero makes the coefficient "
                + "zero. If the cardinalities differ, the same tail subset cannot "
                + "make both total row counts equal k, so every summand is zero.")),
            Paragraph(Text(
                "The Boolean-word/subset equivalence sends a to the finite set "
                + "of sites at which a is true. Under literal Fin.append it sends "
                + "ab to S(a) disjoint-union S(b), mapped by finSumFinEquiv. "
                + "Reindexing the tail-subset sum through this equivalence gives "
                + "the literal tail-word sum defining R. Finset.prod_ite rewrites "
                + "the occupied and unoccupied products as p(a). This establishes "
                + "every matrix entry simultaneously, including unequal prefix "
                + "particle sectors. No inverse, strictly interior eigenvalue, "
                + "Gaussianity, covariance or desired density realization is "
                + "used as a premise.")),
            Paragraph(Text(
                "The interval bounds also come from V. The full matrix "
                + "P_full = V V adjoint is positive semidefinite and idempotent. "
                + "Consequently I - P_full = (I - P_full) adjoint (I - P_full) "
                + "is positive semidefinite. Compress both matrices to the first "
                + "ell sites. Their diagonal entries are nu(i) and 1 - nu(i), "
                + "so Matrix.PosSemidef.diag_nonneg gives 0 at most nu(i) at most "
                + "1 for every one of the ell indices. The proof keeps repeated "
                + "values and zero or one values, with no discarded null space. "
                + "It includes k = 0, k = N, ell = 0, ell = N and N = 0; "
                + "empty determinants and empty products are one.")),
            Paragraph(Text(
                "There is an actual application to the Hermitian spectral basis. "
                + "For the original P = X X adjoint let Q be its eigenvectorUnitary "
                + "and nu its complete Fin ell eigenvalue list. Define W by "
                + "replacing the prefix rows X by Q adjoint X and retaining the "
                + "same tail rows Y. Block multiplication gives W adjoint W = I, "
                + "and Matrix.IsHermitian.spectral_theorem gives the actual "
                + "prefix compression of W as diag(nu). The kernel calculation "
                + "therefore gives R_W = diag(p) and all the interval bounds. "
                + "Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal "
                + "with the identity unitary gives a permutation of the entire "
                + "Boolean occupation carrier identifying the eigenvalues of R_W "
                + "with p. Thus it retains all 2 to the ell values with their "
                + "multiplicities, including zeros.")),
            Paragraph(Text(
                "For this rotated actual marginal the spectral entropy is the "
                + "sum over i in Fin ell of Real.binEntropy(nu(i)). Indeed, "
                + "Finset.prod_univ_sum gives sum over a of p(a) = 1. Split an "
                + "occupation word into its first Boolean coordinate and its "
                + "remaining coordinates with Fin.consEquiv. The identity "
                + "Real.negMulLog_mul and that normalization sum reduce the "
                + "spectral sum by one coordinate. Finite induction gives "
                + "the sum of Real.negMulLog(nu(i)) and "
                + "Real.negMulLog(1 - nu(i)), which is Real.binEntropy(nu(i)). "
                + "The identity uses Real.negMulLog_zero, so it includes singular "
                + "states and the empty prefix. These coefficient, basis and "
                + "spectral applications reuse existing declarations and introduce "
                + "no new mathematical declaration or originality claim.")),
            Paragraph(Text(
                "The original-basis target remains the complete unitary "
                + "diagonalization and von Neumann entropy of R_V. Its remaining "
                + "integrated application is to substitute U = Q adjoint into "
                + "the actual covariance derived above, giving "
                + "R_W = Gamma_ell(Q adjoint) R_V Gamma_ell(Q adjoint) adjoint, "
                + "and combine that identity with R_W = diag(p) on the very "
                + "same Boolean carrier. The expected unitary for R_V is "
                + "Gamma_ell(Q adjoint) adjoint. The complete eigenvalue "
                + "permutation supplier then applies, and the original "
                + "entropy_eq_spectral supplier connects the density state's "
                + "von Neumann entropy to the spectral sum. The original-basis "
                + "spectrum and von Neumann entropy require this combined "
                + "covariance and entropy application; they are not asserted "
                + "by the diagonal-compression calculation alone. "
                + "The k by k particle Gram spectrum is not a replacement for "
                + "the complete ell spatial modes. The Slater two-point formula, "
                + "noncontiguous subsystems with their fermionic ordering, physical "
                + "ground-state selection, filling, many-body gaps and spatial "
                + "entropy scaling retain their separate obligations.")),
            Paragraph(Text(
                "Application: commuting terminal menus on a common two-qubit source. "
                + "Let A = M = C squared, let rho be any positive semidefinite trace-one "
                + "matrix on A tensor M, and let E(c,b) be a finite calibrated menu. "
                + "Every effect and its identity complement are positive semidefinite, "
                + "each setting sums to the identity, and every two effects commute, "
                + "including effects from different settings. The same rho is fixed "
                + "before all setting and outcome quantifiers. The record is the entire "
                + "unnormalized matrix partialTraceRight((I tensor E(c,b)) rho).")),
            Paragraph(Text(
                "Flatten the menu using its dependent setting-outcome index. "
                + "Matrix.commute_euclideanLin and the pinned Mathlib joint-eigenspace "
                + "decomposition for a pairwise commuting symmetric family supply a "
                + "common orthonormal eigenbasis b(j). Restricting to nonzero joint "
                + "eigenspaces gives a finite independent family; its subordinate "
                + "orthonormal basis has two vectors. Thus the common basis is derived "
                + "from the actual effects. Scalar menus and an empty setting carrier "
                + "require no nontrivial-effect assumption.")),
            Paragraph(Text(
                "Put P(j) = b(j) b(j) adjoint and define the rectangular inclusion "
                + "R(j)((a,m),a') = delta(a,a') b(j)(m). The actual blocks are "
                + "D(j) = R(j) adjoint rho R(j), and K(j) = I tensor P(j) = "
                + "R(j) R(j) adjoint. Positivity under compression gives D(j) positive "
                + "semidefinite. Orthonormality gives P(j) squared = P(j), trace(P(j)) "
                + "= 1, and sum P(j) = I. Finite matrix algebra gives the same matrix "
                + "omega = sum K(j) rho K(j) = sum D(j) tensor P(j). Cyclicity of "
                + "trace and sum K(j) = I give sum trace(D(j)) = trace(rho) = 1. "
                + "Consequently omega is positive semidefinite and has trace one.")),
            Paragraph(Text(
                "This is normalized finite convex separability, including zero blocks. "
                + "Take the real weight p(j) = Re trace(D(j)). Positivity makes it "
                + "nonnegative and makes the trace real. If p(j) is positive, take "
                + "alpha(j) = D(j)/p(j); if p(j) is zero, the positive-semidefinite "
                + "zero-trace criterion gives D(j) = 0, and alpha(j) can be the fixed "
                + "density diag(1,0). In both cases D(j) = p(j) alpha(j), with "
                + "alpha(j) positive semidefinite of trace one. With beta(j) = P(j), "
                + "omega is the sum of p(j) alpha(j) tensor beta(j), and sum p(j) = 1. "
                + "No division by a zero trace or removal of a zero outcome is used.")),
            Paragraph(Text(
                "Each actual effect commutes with every P(j). For every path matrix O, "
                + "Kronecker multiplication, cyclicity of trace, idempotence of K(j), "
                + "and sum K(j) = I give trace((O tensor E(c,b)) omega) = "
                + "trace((O tensor E(c,b)) rho). The trace_mul_kron_one_right supplier "
                + "identifies these with pairings against the corresponding partial "
                + "traces. Matrix.ext_iff_trace_mul_left then gives equality of the "
                + "full conditional matrices simultaneously for all settings and outcomes, "
                + "including their probabilities and populations. Taking the identity "
                + "effect preserves the reduced path state; menu completeness makes "
                + "each sum of conditional matrices equal to that same reduced state.")),
            Paragraph(Text(
                "The application uses existing joint-basis, positive-matrix, trace and "
                + "partial-trace results; it introduces no new mathematical declaration. "
                + "For a retained history, apply the construction separately to its "
                + "supplied normalized common conditional source, independent of setting. "
                + "Calibration, conditional tomography, the two-qubit dimension and "
                + "common-source conditions are premises. The conclusion compares "
                + "terminal records and asserts neither a physical preparation procedure "
                + "nor preservation under unperformed coherent reuse. It supplies the "
                + "commuting forward implication only; the converse and Bell-record "
                + "uniqueness require their separate arguments.")),
            Describe.Lean(
                DescribeId.Create("density-positive"),
                DeclarationHandle.Create(Module + "density_posSemidef"),
                H("Density states are positive in matrix coordinates"),
                StatementSource.FromAuthor(DensityPositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The star algebra equivalence from CStarMatrix to Matrix preserves nonnegativity, hence positive semidefiniteness."))),
                DescribeRole.Theorem),
            Result("left-positive", "partialTraceLeft_posSemidef",
                "Tracing out the left factor preserves positivity",
                "For arbitrary finite carriers A and B, the reduced matrix is a finite sum "
                    + "of principal submatrices.", PositivityFormula("partialTraceLeft")),
            Result("right-positive", "partialTraceRight_posSemidef",
                "Tracing out the right factor preserves positivity",
                "The same principal-submatrix argument applies to the other factor.",
                PositivityFormula("partialTraceRight")),
            Result("left-trace", "trace_partialTraceLeft",
                "The left partial trace preserves trace",
                "For every joint matrix, summing the reduced diagonal recovers its diagonal sum.",
                TraceFormula("partialTraceLeft")),
            Result("right-trace", "trace_partialTraceRight",
                "The right partial trace preserves trace",
                "Together with positivity, trace preservation gives a normalized marginal.",
                TraceFormula("partialTraceRight")),
            Describe.Lean(
                DescribeId.Create("spectral-entropy"),
                DeclarationHandle.Create(Module + "spectralEntropy"),
                H("Spectral entropy of a Hermitian matrix"),
                StatementSource.FromAuthor(SpectralEntropyFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(Paragraph(Text(
                    "For any Hermitian matrix on a finite carrier, spectralEntropy sums "
                    + "Real.negMulLog over its eigenvalues. On density matrices this is "
                    + "von Neumann entropy in nats, including singular states with "
                    + "the zero-eigenvalue contribution set to zero."))),
                DescribeRole.Definition),
            Result("charpoly-conj-unitary", "charpoly_conj_unitary",
                "Unitary conjugation preserves the characteristic polynomial",
                "For every finite matrix index type, conjugation by a matrix whose adjoint "
                    + "times the matrix is the identity leaves the characteristic polynomial unchanged.",
                CharpolyConjugacyFormula()),
            Describe.Lean(
                DescribeId.Create("mutual-information"),
                DeclarationHandle.Create(Module + "quantumMutualInformation"),
                H("Mutual information of a joint density state"),
                StatementSource.FromAuthor(MutualInformationFormula()),
                AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(Paragraph(Text(
                    "The only input is the joint state. marginalRight retains A and "
                    + "marginalLeft retains B; each is constructed by partial trace."))),
                DescribeRole.Definition),
            Result("product-entropy", "vonNeumannEntropy_productState",
                "Entropy adds on independent product states",
                "The spectrum of the product is the multiset of pairwise eigenvalue products. "
                    + "For any two density states on finite carriers, including singular states, "
                    + "the proof uses the zero value of x log x at zero.", ProductEntropyFormula()),
            Result("product-information", "quantumMutualInformation_productState",
                "Independent product states have zero mutual information",
                "The actual partial traces recover the two factors. Their entropies cancel "
                    + "the entropy of the product by tensor additivity.", ProductInformationFormula()))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/blore2026partialtrace")),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Theorem);

    private static Formula DensityPositivityFormula()
    {
        Formula n = F.Id("n"), rho = F.Id("rho");
        Formula body = new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("Matrix"), Dot, F.Id("PosSemidef"))),
            [new Formula.Apply(Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot,
                F.Id("ofMatrix"), Dot, F.Id("symm"))), [Call("val", rho)])]);
        body = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("rho"), Call("DensityState", n), body);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Seq(Operatorname, Grp(F.Id("Type"))),
            Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", n), CloseBracket, Sp, body)));
    }

    private static Formula PositivityFormula(string partialTrace) => Disp(Seq(
        Forall, Sp, F.Id("M"), Comma, Sp,
        Call("PosSemidef", F.Id("M")), Sp, Rightarrow, Sp,
        Call("PosSemidef", Call(partialTrace, F.Id("M")))));

    private static Formula TraceFormula(string partialTrace) => Disp(Seq(
        Forall, Sp, F.Id("M"), Comma, Sp,
        Call("trace", Call(partialTrace, F.Id("M"))), Sp, Eq, Sp,
        Call("trace", F.Id("M"))));

    private static Formula MutualInformationFormula() => Disp(Seq(
        Call("quantumMutualInformation", Rho), Sp, Eq, Sp,
        Call("vonNeumannEntropy", Call("marginalRight", Rho)), Sp, Plus, Sp,
        Call("vonNeumannEntropy", Call("marginalLeft", Rho)), Sp, Minus, Sp,
        Call("vonNeumannEntropy", Rho)));

    private static Formula SpectralEntropyFormula()
    {
        Formula n = F.Id("n"), rho = F.Id("rho"), h = F.Id("h"), i = F.Id("i");
        Formula matrix = Call("Matrix", n, n, Seq(Mathbb, Grp(F.Id("C"))));
        Formula hermitian = Seq(Operatorname,
            Grp(F.Id("Matrix"), Dot, F.Id("IsHermitian")));
        Formula eigenvalues = Seq(Operatorname,
            Grp(F.Id("Matrix"), Dot, F.Id("IsHermitian"), Dot, F.Id("eigenvalues")));
        Formula negMulLog = Seq(Operatorname, Grp(F.Id("Real"), Dot, F.Id("negMulLog")));
        Formula body = Seq(Call("spectralEntropy", h), Sp, Eq, Sp,
            Sum, Underscore, Grp(i, Colon, n), Sp,
            new Formula.Apply(negMulLog, [new Formula.Apply(eigenvalues, [h, i])]));
        Formula bindH = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("h"), new Formula.Apply(hermitian, [rho]), body);
        Formula bindRho = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("rho"), matrix, bindH);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Seq(Operatorname, Grp(F.Id("Type"))),
            Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", n), CloseBracket, Sp, bindRho)));
    }

    private static Formula CharpolyConjugacyFormula()
    {
        Formula i = F.Id("i"), rho = F.Id("rho"), unitary = F.Id("U");
        Formula matrix = Call("Matrix", i, i, Seq(Mathbb, Grp(F.Id("C"))));
        Formula star = Call("star", unitary);
        Formula conjugate = new Formula.Binary(
            new Formula.Binary(unitary, FormulaBinaryOperator.Multiply, rho),
            FormulaBinaryOperator.Multiply, star);
        Formula hypothesis = new Formula.Relation(
            new Formula.Binary(star, FormulaBinaryOperator.Multiply, unitary),
            FormulaRelationOperator.Equal, Num(1));
        Formula conclusion = new Formula.Relation(
            new Formula.Apply(Seq(Operatorname, Grp(F.Id("Matrix"), Dot, F.Id("charpoly"))),
                [conjugate]), FormulaRelationOperator.Equal,
            new Formula.Apply(Seq(Operatorname, Grp(F.Id("Matrix"), Dot, F.Id("charpoly"))),
                [rho]));
        Formula body = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("rho"), matrix,
            new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("U"), matrix,
                new Formula.Logic(Seq(Open, hypothesis, Close), FormulaLogicOperator.Implies,
                    Seq(Open, conclusion, Close))));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"), Seq(Operatorname, Grp(F.Id("Type"))),
            Seq(OpenBracket, Call("Fintype", i), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", i), CloseBracket, Sp, body)));
    }

    private static Formula ProductEntropyFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, SigmaLower, Comma, Sp,
        Call("vonNeumannEntropy", Call("productState", Rho, SigmaLower)), Sp, Eq, Sp,
        Call("vonNeumannEntropy", Rho), Sp, Plus, Sp,
        Call("vonNeumannEntropy", SigmaLower)));

    private static Formula ProductInformationFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, SigmaLower, Comma, Sp,
        Call("quantumMutualInformation", Call("productState", Rho, SigmaLower)), Sp, Eq, Sp,
        Num(0)));
}
