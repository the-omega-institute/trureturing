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
                        + "sqrt(Re Tr(P(0) D D)); this is reuse of those identities and calculus "
                        + "results, without an additional mathematical declaration.")),
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

    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);

    private static Formula Angle(string x, string y) => Seq(
        Operatorname, Grp(F.Id("arccos")), Open,
        Norm(Seq(Langle, Sp, F.Id(x), Comma, F.Id(y), Sp, Rangle)), Close);
}
