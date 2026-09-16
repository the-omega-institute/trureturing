using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class TwoPulseCovarianceTomographyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Monodromy/TwoPulseCovarianceTomography."
            + "bounded_two_pulse_covariance_recovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two bounded, coupling-calibrated shear pulses isolate an actual covariance "
            + "entry, with a deterministic error bound independent of leaf-leaf coupling.",
        H("Bounded Two-Pulse Covariance Tomography"),
        Blocks(
            Paragraph(Text(
                "Let H be any real matrix on a finite index type I with decidable "
                    + "equality. Let e_r be the standard coordinate vector. The actual "
                    + "dual pulse is D_i(t)v=(1+t N_i(H-transpose))v, using the "
                    + "repository's row-supported matrix increment. This is the "
                    + "coefficient action on linear readouts ell=Hx of the natural "
                    + "pulse x -> (1+t e_i H_i)x. An interpretation as a Hamiltonian "
                    + "or Gaussian-unitary operation separately requires nonsingular "
                    + "alternating H and the appropriate continuous-variable representation.")),
            Paragraph(Text(
                "Fix a,i,j with alpha=H_ai and beta=H_aj both nonzero. Put "
                    + "c=alpha H_ij. Choose s=1 when beta c is nonnegative and s=-1 "
                    + "otherwise, and t=beta/(beta+s c). Let v0=e_a, "
                    + "vi=D_i(s)e_a, vj=D_j(1)e_a and vij=D_j(t)vi. "
                    + "For a symmetric bilinear covariance B, write Q(v)=B(v,v).")),
            Describe.Lean(
                DescribeId.Create("bounded-two-pulse-covariance-recovery"),
                DeclarationHandle.Create(Declaration),
                H("Bounded controls, exact recovery, and finite-precision certificate"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem proves abs(s)=1, abs(t)<=1 and "
                            + "vij=e_a+s alpha e_i+beta e_j. For every symmetric "
                            + "real bilinear B it then proves "
                            + "[Q(vij)-Q(vi)-Q(vj)+Q(v0)]/(2 s alpha beta)=B(e_i,e_j). "
                            + "Finally, for any epsilon>=0 and four real records "
                            + "z2,zi,zj,z0 within epsilon of these respective actual "
                            + "variances, the same four-record estimator differs "
                            + "from B(e_i,e_j) by at most 2 epsilon/abs(alpha beta).")),
                    Paragraph(Text(
                        "The input does not assert that the routing denominator "
                            + "is nonzero. Sign selection proves beta(s c)>=0 and "
                            + "hence abs(beta+s c)>=abs(beta)>0. This simultaneously "
                            + "justifies the division and the control-amplitude bound. "
                            + "Direct multiplication of the actual pulse matrices "
                            + "then yields the required ray; only after this step "
                            + "is bilinear polarization applied to cancel all nuisance "
                            + "diagonal and anchor terms. Four absolute-error bounds "
                            + "give the stated inverse error certificate. H_ij can "
                            + "be arbitrarily large or vanish without changing this "
                            + "bound, provided the stated control is implemented exactly.")),
                    Paragraph(Text(
                        "The ordinary theory assembles this pairwise construction "
                            + "with the zero-pulse and signed single-pulse settings "
                            + "into n(n+1)/2 covariance settings at depth at most two. "
                            + "It also gives a physical Gaussian covariance pair "
                            + "indistinguishable by every single-pulse homodyne law "
                            + "and separated by two pulses. Those global counting "
                            + "and Gaussian-state existence statements are ordinary "
                            + "mathematical proofs, not extra declarations exported here.")),
                    Paragraph(Text(
                        "The Lean object is a real symmetric bilinear covariance, "
                            + "not a newly defined density matrix or a finite-dimensional "
                            + "exact CCR model. Gaussian uniqueness, uncertainty "
                            + "physicality and metaplectic implementation are separate "
                            + "external mathematical inputs. Finite record errors "
                            + "are assumed certified; no concentration theorem, "
                            + "unknown-Hamiltonian estimate, pulse-calibration error "
                            + "or non-Gaussian complete tomography is claimed.")),
                    Paragraph(Text(
                        "Relevant prior work includes Rall, Gaussian Dynamical "
                            + "Quantum State Tomography, arXiv:2602.18044, and Roh "
                            + "et al., Experimental Quantum State Tomography of "
                            + "Multimode Gaussian States, arXiv:2603.21380. Gaussian "
                            + "moment tomography and generic covariance-setting counts "
                            + "are established ideas. The present construction uses "
                            + "switchable calibrated shears; it does not contradict "
                            + "a restriction for a single autonomous Gaussian evolution. "
                            + "Global priority has not been established."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, F.Id("H"), Comma, Sp, F.Id("a"), Comma, Sp,
        F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
        Call("NonzeroAnchorPair", F.Id("H"), F.Id("a"), F.Id("i"), F.Id("j")),
        Sp, Rightarrow, Sp,
        Call("BoundedActualTwoPulseRay", F.Id("H"), F.Id("a"), F.Id("i"), F.Id("j")),
        Sp, Land, Sp,
        Forall, Sp, F.Id("B"), Comma, Sp, Call("Symmetric", F.Id("B")),
        Sp, Rightarrow, Sp, Call("ExactFourVarianceRecovery", F.Id("B")),
        Sp, Land, Sp, Call("CertifiedFourRecordError", F.Id("B"))));
}
