using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockFockNormalFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual arbitrary-word half-Fock normal fields and their finite-charge source extension.",
        H("Actual Half-Fock Normal Fields"),
        Blocks(
            Paragraph(Text("Let D be any LatticeData and hu:IsUnit D.G.det. The determinant hypothesis is used by the existing actual twisted ground representation. The target is exactly ActualTensor(D,hu)=Oscillator(D) tensor ActualGround(D,hu), with the supplier's groundRank, groundRepresentation and groundAction. Rank zero and indefinite Gram matrices are included. There is no positivity assumption, oscillator occupation bound, homogeneous-source restriction, replacement ground representation, or restriction to a generating set of charges. The seed A is any NativeField(D,hu), and every finite list of indices (colour,order) is permitted, including the empty list and repeated occurrences.")),
            Paragraph(Text("For original mode j, jetScalar(k,j) is the product of -j-3/2-r for 0<=r<k divided by k!, and jetCurrent is this scalar times the actual tensorCurrent. Every recursive coefficient step retains the original j<0 split: a negative mode multiplies on the left, while a nonnegative mode multiplies on the right. Its seed coefficient index changes by e+2*j+2*order+3. No split at a derivative-shifted mode and no ordinary normalMinusOne is substituted. J(word)=sum(2*order+3); n=length(word); S(modes)=sum of original modes. Consequently the exact factorization is leftAction times A.coeff(e+2*S+J) times rightAction.")),
            Paragraph(Text("The current Heisenberg relation makes all nonnegative original modes commute on the actual tensor module. tensor_current_truncation supplies, for each actual vector v, one natural c valid for every colour. Nonzero terms force each original mode to be less than c. Negative modes have no right action, so rightCode replaces each negative mode by -1 and preserves the exact rightAction. These codes lie in the finite box [-1,c]^word. Let L be the minimum of zero and the orders of A applied to all right actions of that finite box. Nonzero factorized terms require L<=e+2*S+J. This bounds the joint mode support for each fixed e,v; it is never support in Module.End and never a globally finite family of operators.")),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-factorization"),
                DeclarationHandle.Create(Prefix + "flatCoefficient_factorization"),
                H("The exact arbitrary-word original-mode factorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For all D,hu, seeds A, finite words w, mode tuples m and integer exponents e, flatCoefficient(D,hu,A,w,m,e)=leftAction(D,hu,w,m)*A.coeff(e+2*modeSum(D,w,m)+jetShift(D,w))*rightAction(D,hu,w,m). Induction preserves the actual ordered operators, negative-left/nonnegative-right convention and original jet shifts. The seed-index lower estimate consumes this identity before any sum is formed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-support-bound"),
                DeclarationHandle.Create(Prefix + "flatTerm_support_bound"),
                H("A pointwise finite box for every joint mode tuple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For any actual v, integer e and natural c that kills all original tensorCurrent modes j>=c on v, support(flatTerm(D,hu,A,w,e,v)) is contained in modeBox(w,min(L-e-J,0)-n*c,c), with L=flatLower(D,hu,A,w,v,c). The premise belongs to this internal estimate. The public finiteness and lower-truncation results obtain c from the existing actual tensor current theorem and impose no cutoff on their callers. The joint lower bound uses the finite right-action minimum and a lower bound on modeSum, not iterated unproved operator-valued sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-pointwise-finite"),
                DeclarationHandle.Create(Prefix + "flatTerm_finite"),
                H("Finite support after applying to every actual tensor state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every D,hu,A,w,e and actual vector v, the function of all mode tuples flatTerm(D,hu,A,w,e,v) has finite support. tensor_current_truncation supplies its cutoff internally. wordCoefficient(e)v is the finsum of this vector-valued function. Additivity uses the two separately proved finite supports at v and u; scalar compatibility uses the finite support at v. Only these proofs make wordCoefficient an actual complex-linear endomorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-derived-truncation"),
                DeclarationHandle.Create(Prefix + "wordCoefficient_lower_truncation"),
                H("Derived lower truncation of the actual word coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every D,hu,A,w and actual vector v, there exists an integer lower such that wordCoefficient(D,hu,A,w,e)v=0 for every integer e<lower. To derive it, obtain c by tensor_current_truncation, and put lower=L-2*n*c-J. A nonzero summand has S<=n*c and L<=e+2*S+J, hence lower<=e. Below this bound every summand is zero. The proof therefore establishes BddBelow support and its IsWF/IsPWO consequence, which wordField passes to HVertexOperator.of_coeff. Neither lower truncation nor finite endomorphism support is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-field-coefficient"),
                DeclarationHandle.Create(Prefix + "wordField_coefficient"),
                H("The constructed Hahn field has the actual pointwise mode sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For all D,hu,A,w,e,v, (wordField(D,hu,A,w)).coeff(e)v equals finsum_m flatTerm(D,hu,A,w,e,v,m). This coefficient identity is the of_coeff interface consumed by sourceField_coefficient; its proof is a binding step, not a separate mathematical novelty. The actual construction is the pointwise linear map and derived bound preceding it. In particular the empty word sums over Unit and recovers A."))),
                DescribeRole.Theorem),
            Paragraph(Text("chargedWordField uses exactly chargedField(D,hu,a) as its seed, for every integral charge a. That existing seed retains chargeNorm=B(a,a), chargeScalar=2^(-B(a,a)), the native half-creation/translation coefficients and the actual groundAction(a). occurrences(d)=d.toMultiset.toList enumerates each natural exponent with its multiplicity. polynomialField extends the corresponding charged word fields by basisMonomials.constr over every oscillator polynomial. sourceField is Finsupp.lsum of these linear maps over the existing ordinary source Carrier(D)=Charge(D) ->finitely-supported Oscillator(D). Thus it is a linear map from every finite-charge source to genuine Hahn fields acting on all actual twisted states. This construction chooses the canonical occurrence list; independence of other occurrence enumerations is not asserted here.")),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-full-source-coefficient"),
                DeclarationHandle.Create(Prefix + "sourceField_coefficient"),
                H("Finite charge and monomial extension of the actual coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For all D,hu, source u:Carrier(D), integer e and actual target v, (sourceField(D,hu)u).coeff(e)v is the finite sum over a in u.support and d in the monomial-basis representation support of u(a), of repr(u(a))(d) times finsum_m flatTerm(D,hu,chargedField(D,hu,a),occurrences(d),e,v,m). The outer sums are finite native source supports; the innermost sum is pointwise in ActualTensor. This binding identity is consumed in the full-source truncation proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-full-source-truncation"),
                DeclarationHandle.Create(Prefix + "sourceField_lower_truncation"),
                H("A derived bound for every finite-charge inhomogeneous source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For all D,hu,u:Carrier(D) and actual v, there exists an integer lower such that (sourceField(D,hu)u).coeff(e)v=0 whenever e<lower. One cutoff c for v suffices. For each supported monomial at each charge, use L-2*n*c-J for its actual charged seed. polynomialLower takes the finite minimum with zero over monomials, and sourceLower the finite minimum with zero over charges. The coefficient formula and wordCoefficient_vanish kill every term below sourceLower. Empty supports, rank zero, arbitrary word length and negative integer exponents are covered by the same proof."))),
                DescribeRole.Theorem),
            Paragraph(Text("Source provenance: the preserved arbitrary-word support candidate is the 347-line LatticeHalfFockFockNormalField.SOURCE.lean supplied with the converged design. The candidate identifies its prior supplier extraction by SHA256 da8469c7f1a7b7c8b9f6be6c48a7e83f9f5154d57c5309958d9806342273ecea; this is inherited attribution, not a hash of the present file or a native acceptance claim. Its ActualGround/ActualTensor, original jet scalar, mode tuple, actions, factorization, rightCode, finite minimum and support estimate are preserved, with the seed-index argument shared privately by support and truncation. The duplicate tensor-induction finiteness supplier is replaced by the existing tensor_current_truncation. New work is the consumed exponent estimate, pointwise linear coefficients, actual Hahn-field packaging, actual charged seed and native basis/finite-charge extension with its explicit finite-minimum bound.")),
            Paragraph(Text("The native current/tensor architecture retains Kalle Kytola's 2025 copyright, Apache-2.0 notice and the additional 2026 half-integer implementation notice. Finite-support, contraction and induction architecture comes through VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 and completed trureturing PolynomialFock sources at bfd9ff0f15397a4fb933f36d701a60d325d84b08. These are architectural sources, not an imported arbitrary-word half-Fock theorem. Mathematical context: Dong-Nagatomo, math/9808088v1, section 3.2, PDF pp.12-14, especially oscillator tensor ground and Delta on p.13; rank/16 is on p.19, proof of Theorem 3.13(3), attributed there to FLM. Bakalov-Kac, math/0402315v1, (4.4) and pp.10-13, (4.23)-(4.38), supplies twisted-current/field context. FLM and FHL full texts were not retrieved by this source phase. No mathematical or literature novelty is claimed.")),
            Paragraph(Text("The proof scope includes arbitrary-word pointwise finite support, derived lower truncation and finite-charge source extension on the actual dependent tensor module. Registration remains unfinished: all seven records are declared_unresolved, none declared_validated. Each is blocked at source.dictionary_or_proof_coordinate because hu is selected as lexical proof coordinate 1. Issue https://github.com/the-omega-institute/trureturing/issues/17623 covers all seven displayed source theorems and this hu-dependent boundary. Compiled typed Reg proof terms do not establish accepted source binding or certificates, and an unknown continuation supplies no residual certificate.")),
            Paragraph(Text("The scientific residual remains: consume actual charged coordinate monodromy; prove the arbitrary-polynomial normal parity law including inhomogeneous inputs and negative exponents; prove the pure Corr(-a,sigma p)[s]=sigma(Corr(a,p)[s]) law with the original singleton/pair derivations; then construct the actual finite corrected field with coefficient index e+2*s and prove its own truncation and unrestricted all-source two-sheet covariance. The shift dictionary is S_s(A)[e]=A[e+2*s], t^(-2*s)=z^(-s), with z=t^2. This normal supplier does not identify itself with that corrected field. Ordered normal-field identities, corrected all-state translation/BPZ, twisted locality/Jacobi/Borcherds, conformal identification, twisted intertwiners, holomorphic extension, Leech/Monster, anomalies/fusion, full CFT, string theory and the AdS/CFT bridge remain downstream obligations.")),
            Paragraph(Ref("D5/L/VertexAlgebra/bakalovkac2004lattice")),
            Paragraph(Ref("D5/L/VertexAlgebra/kytola2025virasoro")),
            Paragraph(Ref("D5/L/VertexAlgebra/flm1988monster")))));
}
