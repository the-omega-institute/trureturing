using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class MatrixUnitDecoderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made.",
        H("MatrixUnitDecoder"),
        Paragraph(Text("ST40.3 application to the actual smooth channel. Take the finite complex channel family N from WholeSmoothRecovery.whole_original_ST37, with its original compact smooth parameter space, complete positivity, trace preservation, CPTP left inverses, constant rank k d, and d>0. Along a path gamma, set Qenc(t)=N(gamma(t))(I), P(t)=spectralSupport(Qenc(t)), W(t)=spectralInverseSqrt(Qenc(t)), pi_t(A)=W(t)N(gamma(t))(A)W(t), and F_ij(t)=pi_t(e_ij). Linearity and the finite matrix-unit expansion identify this actual spectral pi_t(A) with representedMatrix(F(t),A) for every complex A; the diagonal sum identifies unitSupport(F(t)) with this actual P(t). The ST37 returned algebra fields give N(gamma(t))(A)=Qenc(t)pi_t(A), commutation, multiplicativity and adjoints.")),
        Paragraph(Text("Use the actual tangent Dvel of F and K(t)=transportGenerator(F(t),Dvel(t)). On [0,T] with T>=0, assume the original continuity and within-derivative hypotheses. For T>0, MatrixUnitDyson.constructive_transport returns two-sided unitarity of G=dysonSeries(K) and F_ij(t)=G(t)F_ij(0)G(t)†. For T=0 use the actual ambient derivative at zero; MatrixUnitGenerator.generator_from_real_path derives the generator identity from the actual matrix-unit laws, while G(0)=I settles transport. Given the original continuous Hermitian hL and hbar>0, Delta>0, use VL=dysonSeries((-i/hbar)hL) and the literal physical propagator V(t)=G(t)[representedMatrix(F(0),VL(t))+exp(-i Delta t/hbar)(I-unitSupport(F(0)))]. These are the objects in the physical-dynamics application of MatrixUnitDyson; its dynamical proof is reused.")),
        Paragraph(Text("Let Qtilde(t)=G(t)Qenc(0)G(t)†. Complete positivity of the actual N(gamma(0)) makes Qenc(0) positive semidefinite. The ST37 factorization at I and commutation give P(0)Qenc(0)=Qenc(0)P(0)=Qenc(0). Transport and the inverse equations for G therefore give positivity of Qtilde, P(t)Qtilde=Qtilde P(t)=Qtilde, and commutation with every actual F_ij(t). Trace preservation of N(gamma(0)) gives trace(F_vv(0)Qenc(0))=trace(N(gamma(0))(e_vv))=1 for the original reset index v=0; cyclicity and transport give trace(F_vv(t)Qtilde(t))=1. This weight is the transported initial encoding weight; no equality with Qenc(t) is required.")),
        Paragraph(Text("Fix D_t before choosing A: it is exactly ST37's MatrixMap.of_kraus map on the combined decoderKraus(F(t),v,b) and reset matrices e_vb(I-P(t)). ST37 returns complete positivity, trace preservation, and (D_t X)_ij=trace(F_ji(t)X)+trace((I-P(t))X)(e_vv)_ij for every physical X. Transport and trace cyclicity identify D_t(G(t)XG(t)†)=D_0(X) for every X. The supported channel factorization kills both complement cross terms in V(t)N(gamma(0))(A)V(t)†, including the signed phase, and gives the literal output Qtilde(t)pi_t(VL(t)A VL(t)†). Both left and right complement products vanish. Applying the fixed decoder and the actual ST37 recovery field at zero proves D_t(V(t)N(gamma(0))(A)V(t)†)=VL(t)A VL(t)† for every complex logical A and every allowed t. This is a matrix identity, with no density-state restriction, global syndrome frame, physical nonemptiness or full-rank hypothesis; zero complement is included. The full-algebra closed-loop theorem under the same canonical Theta remains a separate application.")),
        Blocks(new[]
        {
            "decoder_kraus_gram",
            "decoder_trace_pairing",
            "matrix_unit_decoder_channel",
            "represented_matrix_mul",
            "decoder_recovers_commutant_weight"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/MatrixUnitDecoder." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/benykempfkribs2007observables"), LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
            Blocks(Paragraph(Text("Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made."))),
            DescribeRole.Theorem)).ToArray())));
}
