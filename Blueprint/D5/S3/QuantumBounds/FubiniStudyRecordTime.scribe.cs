using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class FubiniStudyRecordTimeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumBounds/FubiniStudyRecordTime.";
    private static readonly LibraryNoteRef Geometry =
        LibraryNoteRef.Create("D5/L/Quantum/quair2026projectiveangle");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fubini–Study triangle inequality gives a recording-time bound under assumed speed bounds.",
        H("Fubini–Study Angles and Recording Time"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-vectors-obey-the-fubini-study-triangle-inequality"),
                DeclarationHandle.Create(Module + "fs_angle_triangle"),
                H("The angle of the overlap modulus satisfies the triangle inequality"),
                StatementSource.FromAuthor(Disp(Seq(
                    Norm(F.Id("a")), Eq, Norm(F.Id("b")), Eq, Norm(F.Id("c")), Eq, D(1),
                    Sp, Rightarrow, Sp, Angle("a", "c"), Le,
                    Angle("a", "b"), Plus, Angle("b", "c")))),
                AssessedProvenance.FromLiterature(Geometry),
                Blocks(
                    Paragraph(Text(
                        "For unit vectors in any complex inner product space, the Fubini–Study "
                        + "angle is arccos of the modulus of their complex inner product. The "
                        + "two endpoint phases can be chosen so that their adjacent overlaps "
                        + "with the middle vector are real and nonnegative. The real-angle "
                        + "triangle inequality then bounds the unchanged endpoint overlap modulus.")),
                    Paragraph(Text(
                        "This adapts QuAIR's finite-dimensional pure-vector proof. On vectors "
                        + "the angle is insensitive to phase; separation of points belongs to "
                        + "the space of rays. No quotient-space metric instance is constructed here.")),
                    Paragraph(Text(
                        "The local speed formula is an application of the pinned inner-product "
                        + "and one-variable calculus library. Let f be real differentiable at zero, "
                        + "f(0)=psi, f'(0)=v, and assume norm(f(t))=norm(psi)=1 near zero. "
                        + "Put g(t)=f(t)-inner(psi,f(t)) psi, with the inner product linear in "
                        + "its second slot and complex scalars acting on the left. Orthogonal "
                        + "decomposition gives norm(g(t)) squared = 1-abs(inner(psi,f(t))) squared, "
                        + "so fsAngle(psi,f(t))=arcsin(norm(g(t))). The slope limit and the "
                        + "derivative of arcsin at zero give fsAngle(psi,f(t))/abs(t) tending to "
                        + "sqrt(norm(v) squared-abs(inner(psi,v)) squared). This uses "
                        + "HasDerivAt.inner, HasDerivAt.sub, HasDerivAt.smul_const, "
                        + "HasDerivAt.tendsto_slope, Real.hasDerivAt_arcsin and "
                        + "HasDerivAt.continuousAt_div.")),
                    Paragraph(Text(
                        "In finite complex dimension, differentiating the actual rank-one map "
                        + "P(t)=rankOne(f(t),f(t)) gives D=rankOne(psi,v)+rankOne(v,psi). "
                        + "Differentiating unit norm gives Re inner(psi,v)=0. The identities "
                        + "InnerProductSpace.comp_rankOne, InnerProductSpace.trace_rankOne and "
                        + "LinearMap.trace_comp_comm' then give Re Tr(P(0) D D) = "
                        + "norm(v) squared-abs(inner(psi,v)) squared. Thus the same speed is "
                        + "sqrt(Re Tr(P(0) D D)), by those identities and calculus results.")),
                    Paragraph(Text(
                        "This amplitude calculation does not supply the original real algebra's "
                        + "complex Hilbert structure H_J, J=L_e, or the identification of "
                        + "rankOne with (I-L_e R_n)/2 on its oriented unit sphere. The sphere "
                        + "differential, the tensor on all tangent pairs with its quarter metric "
                        + "and oriented area normalization, the Berry connection i inner(psi,dpsi), "
                        + "its curvature -2 Im Q, and the phase -Omega/2 modulo 2 pi for every "
                        + "smooth or piecewise smooth closed loop require their own proofs, "
                        + "including patchwise Stokes, transition winding and the 4 pi "
                        + "ambiguity of solid angle."))),
                DescribeRole.Theorem),
            AutonomousHamiltonianApplication(),
            Describe.Lean(
                DescribeId.Create("orthogonal-records-require-contact-time-under-speed-bounds"),
                DeclarationHandle.Create(Module + "record_time_lower_bound"),
                H("Orthogonal final records require contact time"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac, Grp(Pi, Sp, F.Id("hbar")), Grp(D(4), Sp, F.Id("E")), Le, Tau))),
                AssessedProvenance.FromLiterature(Geometry),
                Blocks(
                    Paragraph(Text(
                        "Let a, m0 and m1 be unit vectors, with m0 and m1 orthogonal. Assume "
                        + "positive E and hbar, and assume that each endpoint's angle from the "
                        + "same initial vector a is at most E times tau divided by hbar. "
                        + "Their mutual angle is pi over two, so the triangle inequality yields "
                        + "the displayed lower bound.")),
                    Paragraph(Text(
                        "The two displacement bounds are physical inputs. A speed hypothesis "
                        + "valid at every time supplies them by evaluation at the final time. "
                        + "This conditional theorem does not derive the Mandelstam–Tamm bound "
                        + "or model the Hamiltonian evolution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sequential-record-count-is-bounded-by-total-contact-time"),
                DeclarationHandle.Create(Module + "record_count_upper_bound"),
                H("A total contact-time budget bounds the number of records"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("N"), Le,
                    Frac, Grp(D(4), Sp, F.Id("E"), Sp, F.Id("T")),
                    Grp(Pi, Sp, F.Id("hbar"))))),
                AssessedProvenance.FromLiterature(Geometry),
                Blocks(
                    Paragraph(Text(
                        "For N records, each pair of orthogonal final states has its own common "
                        + "initial state and the same positive E and hbar. Assume both displacement "
                        + "bounds for every record and that the sum of their contact durations is "
                        + "at most T. Summing the preceding time bound gives the count bound. "
                        + "The sum budget represents sequential, nonoverlapping contacts; it is "
                        + "an explicit assumption, not a conclusion about arbitrary parallel devices."))),
                DescribeRole.Theorem))));

    private static DocumentBlock AutonomousHamiltonianApplication() => new DocumentBlock.Section(
        H("Application: autonomous Hamiltonian displacement"),
        Blocks(
            Paragraph(Text(
                "The following is a classical application of the pinned operator and calculus "
                + "library. The frozen triangle statement is geometric; the record-time and "
                + "record-count statements additionally assume endpoint displacement bounds. "
                + "None proves Hamiltonian dynamics. The Mandelstam–Tamm estimate below is "
                + "an application, separate from those frozen statements.")),
            Paragraph(Text(
                "Let E be an arbitrary finite-dimensional complex inner product space, with its "
                + "normed additive group structure, A a continuous complex-linear endomorphism "
                + "satisfying IsSelfAdjoint A, psi a unit vector, and hbar a strictly positive real. "
                + "The inner product is conjugate-linear in its first slot and linear in its second; "
                + "real scalars in vector and operator products are embedded into the complex numbers. "
                + "Define mu=Re inner(psi,A psi), Delta=norm(A psi-mu psi), and "
                + "psi_t=exp((-i t/hbar) A)psi, using the normed-algebra exponential of A. "
                + "The full application telescope and bound are:")),
            new DocumentBlock.DisplayFormula(AutonomousBound()),
            Paragraph(Text(
                "Thus the displacement is arccos of the overlap modulus in radians, with no factor "
                + "of two. Self-adjointness makes inner(psi,A psi) real and identifies Delta squared "
                + "with Re inner(psi,A squared psi)-mu squared. In physical units A, mu and Delta "
                + "have units of energy, t of time, and hbar of energy times time; the exponential "
                + "argument and abs(t) Delta/hbar are dimensionless. Assigning these units does "
                + "not establish a physical realization of E, A or psi.")),
            Paragraph(Text(
                "Center the same operator in the same initial state: B=A-mu I, G=(-i/hbar)B, "
                + "U(s)=exp(sG), v(s)=U(s)psi and w(s)=U(s)(G psi). Finite dimension supplies "
                + "completeness. IsSelfAdjoint.smul_mem_skewAdjoint and "
                + "NormedSpace.exp_mem_unitary_of_mem_skewAdjoint make U(s) unitary for every "
                + "real s. ContinuousLinearMap.norm_map_of_mem_unitary gives norm(v(s))=1 and "
                + "norm(w(s))=c, where c=Delta/hbar. The identity "
                + "LinearMap.IsSymmetric.coe_re_inner_self_apply supplies the real expectation; centering "
                + "gives inner(psi,G psi)=0. ContinuousLinearMap.inner_map_map_of_mem_unitary "
                + "therefore gives inner(v(s),w(s))=0. The exponential derivative "
                + "hasDerivAt_exp_smul_const, composed with continuous-linear evaluation at psi, "
                + "gives v'(s)=w(s). This is the horizontal constant-speed orbit, obtained from "
                + "the actual exponential rather than a speed hypothesis.")),
            Paragraph(Text(
                "Regard E as a real inner product space and set r(s)=Re inner(psi,v(s)). "
                + "Then r(0)=1, abs(r(s))<=1 and r'(s)=Re inner(psi,w(s)), using "
                + "HasDerivAt.inner. The real orthogonal projection psi-r(s)v(s) has squared "
                + "norm 1-r(s) squared by norm_sub_sq_real. Its inner product with w(s) is "
                + "r'(s), because v(s) and w(s) are orthogonal. The Cauchy–Schwarz inequality "
                + "abs_real_inner_le_norm consequently gives "
                + "abs(r'(s))<=c sqrt(1-r(s) squared). No division by r or by its derivative "
                + "is involved.")),
            Paragraph(Text(
                "For 0<=q<1, use f_q(s)=arccos(q r(s)). Since abs(q r(s))<1, "
                + "Real.hasDerivAt_arccos applies with positive denominator "
                + "sqrt(1-q squared r(s) squared). The inequality "
                + "q sqrt(1-r(s) squared)<=sqrt(1-q squared r(s) squared) bounds "
                + "abs(f_q'(s)) by c. Apply "
                + "Convex.norm_image_sub_le_of_norm_hasDerivWithin_le on the whole real line "
                + "between 0 and t to obtain arccos(q r(t))<=arccos(q)+c abs(t). "
                + "Now choose q_n=n/(n+1), for natural n. "
                + "tendsto_natCast_div_add_atTop gives q_n tending to one; "
                + "Real.continuous_arccos and le_of_tendsto_of_tendsto yield "
                + "arccos(r(t))<=c abs(t). This regularization retains the endpoints r=1 and "
                + "r=-1, where differentiating arccos directly would be invalid.")),
            Paragraph(Text(
                "The scalar identity commutes with A. NormedSpace.exp_add_of_commute and "
                + "NormedSpace.algebraMap_exp_comm give "
                + "v(t)=exp(i t mu/hbar) exp((-i t/hbar) A)psi. "
                + "Complex.norm_exp_I_mul_ofReal gives norm(exp(i t mu/hbar))=1, so this "
                + "phase preserves the overlap modulus. Complex.re_le_norm and "
                + "Real.arccos_le_arccos then give "
                + "arccos(norm(inner(psi,psi_t)))<=arccos(r(t))<=abs(t) Delta/hbar. "
                + "The proof works for every real t, including negative and zero time. "
                + "It never divides by Delta or by the overlap modulus: zero variance and "
                + "overlaps of modulus zero or one are included. At Delta=0 it forces zero "
                + "ray displacement at every time; at t=0 the initial overlap is one.")),
            Paragraph(Text(
                "Classical attribution: Deffner and Campbell, Quantum speed limits: from "
                + "Heisenberg's uncertainty principle to optimal quantum control, "
                + "arXiv:1705.08023v2, Section 2.5, equation (23) and equations (28)–(33), "
                + "DOI 10.1088/1751-8121/aa86c6. Equation (23) fixes the overlap-angle convention; "
                + "equation (28) centers the Hamiltonian, and equations (29)–(33) give the "
                + "energy-standard-deviation speed and integrated duration bound. "
                + "The autonomous finite-dimensional specialization has constant Delta. "
                + "The source and its precise applicability are recorded in "),
                Ref("D5/L/HilbertOperators/deffnercampbell2017speedlimits"),
                Text(". This derivation is reuse of classical literature and upstream results, "
                    + "with no claim of research novelty or additional frozen dynamics theorem.")),
            Paragraph(Text(
                "For the record-time application, use psi=a and t=tau with tau>=0. "
                + "A positive resource parameter energy with Delta<=energy gives "
                + "fsAngle(a,psi_tau)<=tau Delta/hbar<=energy tau/hbar, exactly the "
                + "displacement premise of record_time_lower_bound. Both endpoints must share "
                + "the same initial preparation a: for j=0,1, choose a self-adjoint A_j, set "
                + "mu_j=Re inner(a,A_j a), Delta_j=norm(A_j a-mu_j a), and "
                + "m_j=exp((-i tau/hbar) A_j)a with Delta_j<=energy. Unitarity supplies each "
                + "endpoint's unit norm; their mutual orthogonality is an additional hypothesis. "
                + "The symbol E in the displayed record-time formula denotes this positive "
                + "energy parameter, not the vector-space carrier E in the application telescope.")),
            Paragraph(Text(
                "For multiple records the same construction is needed separately for each "
                + "record's common initial preparation and each of its two Hamiltonians, with "
                + "the shared positive energy and hbar bounds. The independent assumption "
                + "sum(tau_i)<=T represents sequential, nonoverlapping contact durations; the "
                + "Hamiltonian calculation does not supply that budget. Identifying the "
                + "mathematical states and Hamiltonians with a physical recorder remains a "
                + "realization requirement. No conclusion about open systems, arbitrary "
                + "feedback or measurement protocols, unbounded operators, physical ontology "
                + "or a universal minimal clock tick follows."))));

    private static Formula AutonomousBound()
    {
        Formula e = F.Id("E");
        Formula a = F.Id("A");
        Formula psi = Seq(Mathrm, Grp(F.Id("psi")));
        Formula hbar = Seq(Mathrm, Grp(F.Id("hbar")));
        Formula t = F.Id("t");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula applied = Seq(a, Sp, psi);
        Formula mu = Seq(Re, Sp, Langle, psi, Comma, applied, Rangle);
        Formula delta = Norm(Seq(applied, Minus, Open, mu, Close, Sp, psi));
        Formula coefficient = Seq(Frac, Grp(Minus, F.Id("i"), Sp, t), Grp(hbar));
        Formula evolved = Seq(Exp, Open, coefficient, Sp, a, Close, Sp, psi);
        Formula overlap = Norm(Seq(Langle, psi, Comma, evolved, Rangle));
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, e, Colon, F.Id("Type"), Comma, Sp,
                OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Sp,
                OpenBracket, Call("InnerProductSpace", complex, e), CloseBracket, Sp,
                OpenBracket, Call("FiniteDimensional", complex, e), CloseBracket, Comma),
            Seq(Amp, Forall, Sp, a, Colon, Call("ContinuousLinearMap", complex, e, e), Comma, Sp,
                Forall, Sp, psi, Colon, e, Comma, Sp,
                Forall, Sp, hbar, Comma, t, Colon, real, Comma),
            Seq(Amp, Call("IsSelfAdjoint", a), Sp, Land, Sp, Norm(psi), Eq, D(1), Sp,
                Land, Sp, D(0), Lt, hbar, Sp, Implies),
            Seq(Amp, Operatorname, Grp(F.Id("arccos")), Open, overlap, Close, Le,
                Frac, Grp(Bar, t, Bar, Sp, delta), Grp(hbar))]));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);

    private static Formula Angle(string x, string y) => Seq(
        Operatorname, Grp(F.Id("arccos")), Open,
        Norm(Seq(Langle, Sp, F.Id(x), Comma, F.Id(y), Sp, Rangle)), Close);
}
