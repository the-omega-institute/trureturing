using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FiniteKrausInstrumentBornMarginalDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal."
            + "finite_kraus_instrument_born_marginal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite normalized Kraus instruments have the expected one-step Born marginal.",
        H("Finite Kraus Instrument Born Marginal"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-kraus-instrument-born-marginal"),
            DeclarationHandle.Create(Declaration),
            H("A finite Kraus branch has the Born weight of its effect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public Kraus family is normalized at every setting, so its "
                        + "outcome branches form a finite-dimensional instrument. The input "
                        + "uses the canonical positive trace-one density-state carrier.")),
                Paragraph(Text(
                    "Each branch and effect is constructed by a finite Kraus sum. Trace "
                        + "linearity and cyclicity move the outer Kraus operator across the "
                        + "trace, yielding the canonical Born trace pairing."))),
            DescribeRole.Theorem), V2Application())));

    private static DocumentBlock V2Application() => new DocumentBlock.Section(
        H("Application: one outgoing V2 environment and initial-mode posteriors"),
        Blocks(
            Paragraph(Text(
                "This is a source-bound application of established finite-instrument, pure-state Gram and Bayes results. "
                + "The derivations below are ordinary mathematics, not a new general discovery or a Lean kernel certificate. "
                + "The exact V2, common-POVM and posterior application bridges remain unverified in Lean. "
                + "The machine-checked theorem above supplies the branch-trace/Born-effect identity for a normalized finite Kraus family; it does not by itself certify these bridges.")),
            new DocumentBlock.Section(H("Source, preparation and measurement assumptions"), Blocks(
                Paragraph(Text(
                    "Fix [Recursive relational observation: minimal pure records, definitions 1.1–1.2 and Theorem 2.1](https://github.com/the-omega-institute/trureturing/blob/363177b65cdef19a5a66ab92860ad70c16e7ad11/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md). "
                    + "Its underlying transported graph is revision 6bfd5342e47ba7eb50a5022e301d228f17daa8d2 of AURIC_FIB_HISTORY_RECORDS_TIME_ARROW, §§126–135. "
                    + "Use the source order (s₀,s₁,s₂,s₃,s₄)=(000,100,101,001,010), with low-to-high words, throughout.")),
                Paragraph(Text(
                    "Let p,q,r>0 and p+q+r<1, t=p+q, B=1−t, A=B−r, C=A+t, γ=√(A/B), and h=B−t. "
                    + "Then B,t,A>0 and 0<γ<1. No p=q restriction or lower probability cutoff is imposed. "
                    + "The source-row/successor-column matrix has rows (A,p,0,q,r), (q,B,p,0,0), (0,q,B,p,0), (p,0,q,B,0), (r,0,0,0,C).")),
                Paragraph(Text(
                    "On H=ℂ⁵⊗K, K=ℂ², use the standard Pauli matrices and exactly a=−iX, b=−iY, c=ba=iZ. "
                    + "The transports are U₁₀=a, U₂₁=c, U₃₂=a†, U₀₃=c†, U₄₀=b, their adjoints on reverse edges, and identity on loops. "
                    + "In particular U₀₄=b†; the alternative §124 assignment is not substituted.")),
                Paragraph(Text(
                    "In a single common orthonormal basis f₀,f₁ of E₂=ℂ², put S=|1⟩⟨0|⊗a+|2⟩⟨1|⊗c+|3⟩⟨2|⊗a†+|0⟩⟨3|⊗c†. "
                    + "The stipulated isometry is V₂ξ=L₀ξ⊗f₀+L₁ξ⊗f₁, where "
                    + "L₀=diag(√A,√B,√B,√B,−√A)⊗I_K+√r(|4⟩⟨0|⊗b+|0⟩⟨4|⊗b†) "
                    + "and L₁=√p S+√q S†+√t |4⟩⟨4|⊗I_K. "
                    + "The source proves L₀†L₀=B I_H and L₁†L₁=t I_H on the full input space.")),
                Paragraph(Text(
                    "Prepare ρ_HR=Σᵢ πᵢ |i⟩⟨i|⊗ρ_KR⁽ⁱ⁾, with πᵢ>0, Σᵢπᵢ=1, and arbitrary normalized positive semidefinite conditional density operators ρ_KR⁽ⁱ⁾. "
                    + "R is any finite-dimensional untouched reference; internal/reference entanglement and singular conditional states are allowed. "
                    + "Apply V₂⊗I_R once. The latent initial mode is a classical analysis variable, not an accessible extra register. "
                    + "V₂ changes the current configuration, so the posterior below concerns the initial mode.")),
                Paragraph(Text(
                    "The decoder has only the actual outgoing E₂, with one supplied POVM (Mₒ) on any nonempty finite outcome set Ω: Mₒ≥0 and ΣₒMₒ=I₂. "
                    + "It has no access to the initial mode, current configuration, K or R. Zero effects are allowed; the same complete family must serve every initial mode. "
                    + "Measurement access, basis calibration, phase control and a retained classical result are separate supplied resources. "
                    + "A POVM specifies likelihoods; a postmeasurement state requires an instrument. One realization is Kₒ=√Mₒ, giving branches τ↦KₒτKₒ†, whose sum is trace preserving.")))),
            new DocumentBlock.Section(H("The two complementary environment states"), Blocks(
                Paragraph(Text(
                    "Conditioned on initial i, trace out the updated H and R. In the common f₀,f₁ basis the result is "
                    + "D=diag(B,t) for i=0,1,2,3, and F=((B,−√(At)),(−√(At),t)) for i=4, with ordered matrix rows displayed in parentheses. "
                    + "Both have trace one, det D=B t>0 and det F=t r>0, hence are strictly positive.")),
                Paragraph(Text(
                    "Proof. The two diagonal entries are B and t by L₀†L₀=B I and L₁†L₁=t I, independently of each conditional internal/reference state. "
                    + "For i<4 the successor supports of L₀|i⟩ and L₁|i⟩ are disjoint, so the cross partial trace vanishes. "
                    + "For i=4, L₀|4⟩=√r |0⟩⊗b†−√A |4⟩⊗I and L₁|4⟩=√t |4⟩⊗I. "
                    + "Only their common successor 4 contributes, giving −√(At) Tr ρ_KR⁽⁴⁾=−√(At). This proves the claim without measuring R or adding a source label.")))),
            new DocumentBlock.Section(H("Complete finite common-POVM equivalence"), Blocks(
                Paragraph(Text(
                    "Let (aₒ),(bₒ) be nonnegative rows on Ω with Σₒaₒ=Σₒbₒ=1, and δₒ=bₒ−aₒ. "
                    + "There exists one complete POVM with Tr(DMₒ)=aₒ and Tr(FMₒ)=bₒ for every outcome if and only if both conditions hold:")),
                new DocumentBlock.DisplayFormula(CommonPovmFormula()),
                Paragraph(Text(
                    "Necessity. Set Qₒ=D¹ᐟ²MₒD¹ᐟ², so Qₒ≥0, Tr Qₒ=aₒ and Re(Qₒ)₀₁=−δₒ/(2γ). "
                    + "Writing dₒ=(Qₒ)₀₀−(Qₒ)₁₁, positivity of a Hermitian 2×2 matrix gives dₒ²+4|(Qₒ)₀₁|²≤aₒ². "
                    + "Thus |δₒ|≤γaₒ and |dₒ|≤sₒ:=√(aₒ²−δₒ²/γ²). Completeness gives ΣₒQₒ=D, hence Σₒdₒ=h and |h|≤Σₒsₒ. "
                    + "Complex effects are included: imaginary off-diagonal parts only strengthen the positivity bound.")),
                Paragraph(Text(
                    "Sufficiency. Let S_w=Σₒsₒ. If S_w>0 choose dₒ=h sₒ/S_w; if S_w=0 the second condition forces h=0, and choose dₒ=0. "
                    + "Then |dₒ|≤sₒ and Σₒdₒ=h. Define Qₒ=½((aₒ+dₒ,−δₒ/γ),(−δₒ/γ,aₒ−dₒ)) "
                    + "and Mₒ=D⁻¹ᐟ²QₒD⁻¹ᐟ². The inequalities aₒ≥0 and dₒ²+δₒ²/γ²≤aₒ² imply Qₒ≥0. "
                    + "Since Σₒaₒ=1, Σₒδₒ=0 and Σₒdₒ=h, their sum is ½diag(1+h,1−h)=D. "
                    + "Consequently ΣₒMₒ=I₂, every Mₒ≥0, and each Mₒ≤I₂ because its complement is the sum of the other effects.")),
                Paragraph(Text(
                    "Explicitly, Mₒ=½(((aₒ+dₒ)/B,−δₒ/(γ√(Bt))),(−δₒ/(γ√(Bt)),(aₒ−dₒ)/t)). "
                    + "Then Tr(DMₒ)=Tr Qₒ=aₒ and Tr((F−D)Mₒ)=−2√(At)(Mₒ)₀₁=δₒ, proving all required likelihoods.")),
                Paragraph(Text(
                    "Degenerate cases. If aₒ=0, the first condition forces δₒ=bₒ=0 and the construction gives Mₒ=0. "
                    + "Conversely D>0 and F>0 make zero likelihood equivalent to a zero effect, so every nonzero effect has aₒ,bₒ>0. "
                    + "When B=t the summed-width condition is automatic, including S_w=0 with saturated rows. "
                    + "When S_w=0 and B≠t no common POVM exists. A singleton outcome is realized by M=I₂. "
                    + "Any finite number of zero effects may be restored; neither a cardinality cutoff nor division by an outcome likelihood is used.")))),
            new DocumentBlock.Section(H("Established Gram supplier and exact specialization"), Blocks(
                Paragraph(Text(
                    "Anthony Chefles, Richard Jozsa and Andreas Winter, *On the existence of physical transformations between sets of quantum states*, "
                    + "International Journal of Quantum Information 2(1), 11–21 (2004), [DOI 10.1142/S0219749904000031](https://doi.org/10.1142/S0219749904000031), "
                    + "[arXiv:quant-ph/0307227v1, p. 6, Theorem 3, equations (7)–(8)](https://arxiv.org/pdf/quant-ph/0307227v1), "
                    + "supplies the general multi-probabilistic instrument/Gram criterion. "
                    + "The repository already cites it for another specialization in [CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM §6.1](https://github.com/the-omega-institute/trureturing/blob/363177b65cdef19a5a66ab92860ad70c16e7ad11/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md#6-后选择规范化的相干界).")),
                Paragraph(Text(
                    "To identify this application, put ψ₊=√B f₀+√t f₁, ψ₋=√B f₀−√t f₁ and R₊=|ψ₊⟩⟨ψ₊|, R₋=|ψ₋⟩⟨ψ₋|. "
                    + "Their Gram matrix is G=((1,h),(h,1)), while D=(R₊+R₋)/2 and F=((1−γ)R₊+(1+γ)R₋)/2. "
                    + "Thus a common D/F POVM has pure-pair likelihoods ℓₒ⁺=aₒ−δₒ/γ and ℓₒ⁻=aₒ+δₒ/γ. "
                    + "Both rows are normalized, their nonnegativity is exactly |δₒ|≤γaₒ, and Σₒ√(ℓₒ⁺ℓₒ⁻)=Σₒsₒ.")),
                Paragraph(Text(
                    "Specialize Theorem 3 to these two pure inputs and the same fixed pure output for both inputs at each outcome. "
                    + "Every output Gram matrix is all ones, so its Hadamard decomposition reduces to G=ΣₒΠₒ, Πₒ≥0, diag Πₒ=(ℓₒ⁺,ℓₒ⁻). "
                    + "Positivity implies |h|≤Σₒ√(ℓₒ⁺ℓₒ⁻). Conversely, if S_w>0 take (Πₒ)₀₁=h√(ℓₒ⁺ℓₒ⁻)/S_w; "
                    + "if S_w=h=0 take these entries zero. This gives positive Gram contributions summing to G. "
                    + "A common POVM yields the corresponding measure-and-prepare instrument, and an instrument yields its effects, establishing the exact supply relationship. "
                    + "The auxiliary pure pair is an algebraic decomposition, not an additional accessible input label or preparation assumption.")),
                Paragraph(Text(
                    "The instrument conventions are those of John Watrous, *The Theory of Quantum Information* (2018), "
                    + "[Chapter 2, §2.3.2, equations (2.255)–(2.262)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf), "
                    + "[DOI 10.1017/9781316848142](https://doi.org/10.1017/9781316848142). "
                    + "The explicit construction above proves sufficiency for this D/F family; a general mixed-state fidelity inequality alone would not do so.")))),
            new DocumentBlock.Section(H("Five-mode coordinates, posterior fiber and covariance"), Blocks(
                Paragraph(Text(
                    "Use [AURIC_FIB_ATOM_RECORD_SIMPLEX_AND_HIGHER_ORDER_COMPATIBILITY §§1–2, 7, 10](https://github.com/the-omega-institute/trureturing/blob/363177b65cdef19a5a66ab92860ad70c16e7ad11/docs/develop/theory/AURIC_FIB_ATOM_RECORD_SIMPLEX_AND_HIGHER_ORDER_COMPATIBILITY.md) "
                    + "only after the exact coordinate permutation. Source indices (0,1,2,3,4) mean (empty,low,both,high,middle). "
                    + "Its record order (p_empty,p₁,p₂,p₃,p₁₃) is (π₀,π₁,π₄,π₃,π₂). "
                    + "For initial-mode features x,y,z indicating low, high, middle occupancy, X=π₁+π₂, Y=π₃+π₂, Z=π₄, κ=π₂=E[xy].")),
                Paragraph(Text(
                    "Set w=π₄, v=1−w and ηᵢ=πᵢ/v for i<4. An outcome has probability qₒ=v aₒ+w bₒ. "
                    + "On the positive-mixture domain qₒ>0 define uₒ=w bₒ/qₒ. Bayes gives πᵢ⁽ᵒ⁾=(1−uₒ)ηᵢ for i<4 and π₄⁽ᵒ⁾=uₒ. "
                    + "In record order this is ((1−uₒ)η₀,(1−uₒ)η₁,uₒ,(1−uₒ)η₃,(1−uₒ)η₂). "
                    + "All non-leaf odds are fixed: all posteriors lie on this one affine line.")),
                Paragraph(Text(
                    "The rowwise bound gives 1−γ≤bₒ/aₒ≤1+γ on every nonzero outcome, hence "
                    + "w(1−γ)/(1−wγ)≤uₒ≤w(1+γ)/(1+wγ), strictly inside (0,1). "
                    + "No such outcome perfectly identifies the leaf or an individual non-leaf initial mode. "
                    + "Normalization gives Σₒqₒπ⁽ᵒ⁾=π and Σₒqₒuₒ=w.")),
                Paragraph(Text(
                    "For a prescribed positive-weight family (qₒ,uₒ) on this fiber, require qₒ>0, 0≤uₒ≤1, Σₒqₒ=1 and Σₒqₒuₒ=w. "
                    + "Recover aₒ=qₒ(1−uₒ)/v and bₒ=qₒuₒ/w. The complete quantum realization condition is exactly "
                    + "|uₒ−w|≤γw(1−uₒ) for each o, together with "
                    + "Σₒ(qₒ/v)√((1−uₒ)²−(uₒ−w)²/(γ²w²))≥|B−t|. "
                    + "These follow by substituting into the proved equivalence, and the same substitution constructs a common POVM in the reverse direction. "
                    + "Zero-weight outcomes have no defined posterior and may be restored as zero effects.")),
                Paragraph(Text(
                    "Let μ=(X,Y,Z,κ)ᵀ, d=(−X/v,−Y/v,1,−κ/v)ᵀ and V_u=Σ_{qₒ>0}qₒ(uₒ−w)². "
                    + "Subtracting the prior means gives μₒ−μ=(uₒ−w)d, so the record separation covariance is B_rec=V_u d dᵀ. "
                    + "Also V_u=w²v²Σ_{qₒ>0}(bₒ−aₒ)²/qₒ. Thus B_rec has rank zero exactly when every aₒ=bₒ, and rank one otherwise, for any finite outcome count. "
                    + "Its (X,Y,Z) principal covariance has rank at most one and determinant zero, with B_rec,XY=(XY/v²)V_u and B_rec,XZ=−(X/v)V_u.")),
                Paragraph(Text(
                    "For the initial feature vector g=(x,y,z,xy)ᵀ, the total covariance identity is "
                    + "Σₒqₒ Cov(g|O=o)=Cov(g)−B_rec. It follows by expanding g−E[g]=(g−E[g|O])+(E[g|O]−E[g]) and averaging; cross terms vanish by conditional centering. "
                    + "These are classical initial-mode posterior restrictions, not a quantum-entanglement assertion. "
                    + "In particular the separately supplied §7 tetrahedron, whose three-coordinate covariance has rank three and determinant 1/5000, is not produced by this one E₂-only measurement. "
                    + "A separately supplied qubit SIC applied to the actual one-parameter D/F mixture still cannot create three independent initial-mode posterior directions.")),
                Paragraph(Text(
                    "The classical forward and reverse suppliers are [BayesPlausibility](../../ConceptDynamics/ObservationOrder/BayesPlausibility.md) "
                    + "and [PosteriorMixtureKernelRealization](../../ConceptDynamics/ObservationOrder/PosteriorMixtureKernelRealization.md). "
                    + "The general signal-kernel realization is established finite Bayes plausibility; see Kamenica and Gentzkow, *Bayesian Persuasion*, American Economic Review 101 (2011), "
                    + "[Proposition 1](https://web.stanford.edu/~gentzkow/research/BayesianPersuasion.pdf). It does not supply a POVM on this fixed outgoing quantum environment. "
                    + "The SIC supplier is Renes, Blume-Kohout, Scott and Caves, *Symmetric Informationally Complete Quantum Measurements*, "
                    + "[quant-ph/0310075](https://arxiv.org/abs/quant-ph/0310075), [DOI 10.1063/1.1737053](https://doi.org/10.1063/1.1737053).")))),
            new DocumentBlock.Section(H("Individually feasible rows need not form a complete measurement"), Blocks(
                Paragraph(Text(
                    "Take p=1/16, q=3/16, r=9/16. Then p≠q, p+q+r=13/16<1, t=1/4, B=3/4, A=3/16, γ=1/2 and √(At)=√3/8. "
                    + "For four outcomes choose a=(1/4,1/4,1/4,1/4), b=(3/8,3/8,1/8,1/8), both positive normalized rows.")),
                Paragraph(Text(
                    "For σ=+1 on the first two outcomes and σ=−1 on the last two, "
                    + "M_σ=((1/6,−σ/(2√3)),(−σ/(2√3),1/2)) has determinant zero and eigenvalues 0,2/3. "
                    + "Thus 0≤M_σ≤I₂ and the binary POVM (M_σ,I₂−M_σ) individually realizes aₒ=1/4, bₒ=1/4+σ/8. "
                    + "Nevertheless every row saturates |δₒ|=γaₒ and has sₒ=0. The common-family criterion would require 0≥|B−t|=1/2, which is false. "
                    + "Equivalently saturated positivity forces each effect to be the displayed M_σ; their sum is diag(2/3,2), not I₂.")),
                Paragraph(Text(
                    "With πᵢ=1/5, the four outcome weights are (11/40,11/40,9/40,9/40). "
                    + "The first two initial-mode posteriors in source order are (2/11,2/11,2/11,2/11,3/11), "
                    + "and the last two are (2/9,2/9,2/9,2/9,1/9). "
                    + "In record order these become (2/11,2/11,3/11,2/11,2/11) and (2/9,2/9,1/9,2/9,2/9). "
                    + "Their weighted mixture returns each prior coordinate 1/5. The normalized classical kernel with rows a for modes 0–3 and b for mode 4 therefore realizes this Bayes-plausible family. "
                    + "The common quantum measurement is still excluded. This is an explanatory ordinary mathematical example.")))),
            new DocumentBlock.Section(H("Informative phase read versus the correction flag"), Blocks(
                Paragraph(Text(
                    "Measuring the published basis projections |f₀⟩⟨f₀| and |f₁⟩⟨f₁| gives likelihoods (B,t) for every initial mode. "
                    + "Its posterior is always π and B_rec=0. With the separately supplied inverse controls T₀†,T₁†, where T₀=L₀/√B and T₁=L₁/√t, "
                    + "this is the full-input/reference correction flag of the minimal-record source Theorem 2.2. It is not an informative source label or an exact-edge read.")),
                Paragraph(Text(
                    "A separately supplied calibrated Pauli-X measurement on outgoing E₂ has M₊=(I₂+X_E)/2 and M₋=(I₂−X_E)/2. "
                    + "It gives a₊=a₋=1/2 and b₊=1/2−√(At), b₋=1/2+√(At), hence is informative about leaf versus non-leaf because At>0. "
                    + "Each width is |B−t|/2, so the common-POVM bound is attained with equality, including the B=t zero-width stratum. "
                    + "The result must actually be measured and retained. Its system branches use (L₀+L₁)/√2 and (L₀−L₁)/√2. "
                    + "The published flag-recovery theorem does not provide full-input feedback recovery for these informative branches.")),
                Paragraph(Text(
                    "The preparation restriction matters: arbitrary coherent configuration input is not the stipulated classical initial-mode ensemble. "
                    + "Likewise independently supplied arbitrary qubit/SIC preparations, exact source or edge labels, correction controllers, sequential fresh environments on one evolving system, "
                    + "retained histories, independent prepared copies, native FIB acquisition and arbitrary coherent archives are distinct interfaces. "
                    + "Physical preparation, calibration, control and finite precision are additional assumptions. No history count, tomography protocol, indefinite repetition or executable real-parameter calibration follows here.")),
                Paragraph(Text(
                    "The [readout-closure source §§2, 9](https://github.com/the-omega-institute/trureturing/blob/363177b65cdef19a5a66ab92860ad70c16e7ad11/docs/develop/theory/AURIC_FIB_ATOM_READOUT_CLOSURE_AND_RECORD_TRIANGLE.md) "
                    + "uses static classical-mode ports and separately supplied quantum instruments. "
                    + "This application's initial-mode coordinate identification supplies neither a nondemolition mode port nor those coherent instruments. "
                    + "Common-ancestry and directional-alpha conclusions require their own source and operation correspondences. "
                    + "FourQubitParentConstruction and FourQubitCompatibilityDegree concern a joint parent for four dichotomic measurements on one qubit with white noise; "
                    + "that marginal problem does not identify this prescribed D/F likelihood family."))))));

    private static Formula CommonPovmFormula()
    {
        Formula outcome = F.Id("o");
        Formula a = Seq(F.Id("a"), Underscore, Grp(outcome));
        Formula delta = Seq(DeltaLower, Underscore, Grp(outcome));
        Formula gamma = GammaLower;
        Formula squared(Formula value) => Seq(value, Caret, Grp(D(2)));
        return Seq(
            Lvert, delta, Rvert, Sp, Leq, Sp, gamma, Sp, a, Quad,
            Forall, Sp, outcome, Comma, Qquad,
            Sum, Underscore, Grp(outcome), Sp,
            Sqrt, Grp(squared(a), Minus, Frac, Grp(squared(delta)), Grp(squared(gamma))),
            Sp, Geq, Sp, Lvert, Sp, F.Id("B"), Minus, F.Id("t"), Rvert, Dot);
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula TheoremFormula()
    {
        Formula system = F.Id("n"), settingType = F.Id("X");
        Formula outcomeType = F.Id("A"), krausType = F.Id("R");
        Formula family = F.Id("K"), state = Rho, x = F.Id("x");
        Formula outcome = F.Id("a"), k = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", system, system, complex);
        Formula krausAt = Apply(family, x, outcome, k);
        Formula stateValue = F.Id("S");
        Formula branchMatrix = F.Id("B");
        Formula effectMatrix = F.Id("E");
        Formula stateDefinition = Call("matrix", state);
        Formula krausProduct = Multiply(Call("star", krausAt), krausAt);
        Formula normalized = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("x"), settingType)],
            Equal(
                Seq(Sum, Underscore, Grp(outcome, Sp, InMacro, Sp, outcomeType), Sp,
                    Sum, Underscore, Grp(k, Sp, InMacro, Sp, krausType), Sp,
                    krausProduct),
                Call("identityMatrix", system)));
        Formula familyFunctionType = Seq(
            settingType, Sp, To, Sp, outcomeType, Sp, To, Sp,
            krausType, Sp, To, Sp, matrix);
        Formula instrumentType = Seq(
            OpenBrace, family, Colon, Sp, familyFunctionType, Sp, Mid, Sp,
            normalized, CloseBrace);
        Formula branchDefinition = Seq(
            Sum, Underscore, Grp(k, Sp, InMacro, Sp, krausType), Sp,
            Multiply(Multiply(krausAt, stateValue), Call("star", krausAt)));
        Formula effectDefinition = Seq(
            Sum, Underscore, Grp(k, Sp, InMacro, Sp, krausType), Sp,
            krausProduct);
        Formula marginal = Equal(
            Call("Tr", branchMatrix),
            Call("bornProbability", stateValue, effectMatrix));

        return Disp(Seq(
            Forall, Sp,
            system, Comma, Sp, settingType, Comma, Sp,
            outcomeType, Comma, Sp, krausType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Call("Fintype", system), Comma, Sp,
            Call("Nonempty", system), Comma, Sp,
            Call("DecidableEq", system), Comma, RowBreak, Grp(),
            Call("Fintype", outcomeType), Comma, Sp,
            Call("Fintype", krausType), Comma, RowBreak, Grp(),
            family, Colon, Sp, instrumentType, Comma, RowBreak, Grp(),
            state, Colon, Sp, Call("DensityState", system), Comma, RowBreak, Grp(),
            Forall, Sp, x, Colon, Sp, settingType, Comma, Sp,
            outcome, Colon, Sp, outcomeType, Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            stateValue, Colon, Sp, matrix, Sp, Eq, Sp,
            stateDefinition, Comma, RowBreak, Grp(),
            branchMatrix, Colon, Sp, matrix, Sp, Eq, Sp,
            branchDefinition, Comma, RowBreak, Grp(),
            effectMatrix, Colon, Sp, matrix, Sp, Eq, Sp,
            effectDefinition, Semi, RowBreak, Grp(),
            marginal, Dot));
    }
}
