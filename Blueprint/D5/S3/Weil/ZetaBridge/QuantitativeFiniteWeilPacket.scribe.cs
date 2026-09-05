using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class QuantitativeFiniteWeilPacketDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/QuantitativeFiniteWeilPacket.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual multi-orbit Burnol packets are reconstructed with unit support, finite arithmetic interpolation jets and an explicit exceptional radius. The remaining infinite scalar zero-tail estimate is kept separate.",
        H("Quantitative Packets from Certified Finite Zero Nodes"),
        Blocks(
            Describe.Lean(DescribeId.Create("quantitative-packet-reflection-nodes"),
                DeclarationHandle.Create(Prefix + "reflectionNodeSet"), H("The existing sign quotient as a finite catalog"),
                StatementSource.FromAuthor(Disp(F.Id("reflectionNodeSet(Z,E)=image of j -> gamma(reflectionRep(j)) on E."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is exactly the finite image used inside the existing reflection-compatible interpolation proof. Multiplicity copies do not become additional nodes."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitative-finite-zero-interpolation"),
                DeclarationHandle.Create(Prefix + "quantitative_interpolation_on_finite_indices"), H("Finite zero data with explicit jets"),
                StatementSource.FromAuthor(Disp(F.Id("Reflection-compatible data on E with radius R, amplitude V and positive squared-node gap sigma admit an actual unit-supported Weil test with the prescribed values and L1(D^s g)<=J_s(d,R,sigma,V), s<=2."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Descend values through the existing reflection representative, apply the constructed finite-box/Lagrange jet theorem, then transport evaluations back to the original zero indices. The source reuses gamma injectivity and reflectionRep_freq. All new assumptions are finite nodal enclosures or compatibility statements."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitative-peak-radius"),
                DeclarationHandle.Create(Prefix + "quantitativePeakRadius"), H("An explicit exceptional cutoff"),
                StatementSource.FromAuthor(Disp(F.Id("H=R+6*(J_0(d,R,sigma,1)+J_2(d,R,sigma,1))+1."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("R is a bound for the selected target node norms. The remaining terms are finite arithmetic expressions from the interpolation jet theorem. The generous additive radius avoids an existential eventual-smallness threshold."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitative-actual-unit-peak"),
                DeclarationHandle.Create(Prefix + "exists_quantitative_finite_unit_peak"), H("Construct the peak and prove the tail bound"),
                StatementSource.FromAuthor(Disp(F.Id("There is an actual unit-supported peak equal to one on E, with its explicit J0,J2 bounds, E contained in the H-ball, and both conjugate Fourier-Laplace evaluations of norm at most one half outside that ball."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use unit-valued finite interpolation. The already proved half-strip jet bound then implies the explicit cutoff inequality. No unspecified derivative norm or unknown exceptional radius is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitative-actual-burnol-packet"),
                DeclarationHandle.Create(Prefix + "exists_quantitative_orbitBurnolPacket"), H("A complete actual finite packet from two finite catalogs"),
                StatementSource.FromAuthor(Disp(F.Id("A valid orbit frame, a certified target radius and gap, and a certified positive gap for the explicitly determined exceptional catalog yield an actual OrbitBurnolPacket with B=K=1 and common killer jets J_s(d_E,H,tau,1)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("First construct the quantitative common peak. Its arithmetic H determines E=symmetricIndices(H). Then interpolate each signed orbit assignment on that same E, using the second certified gap tau. The assignments have magnitude at most one. The resulting packet satisfies the original target values, finite exception annihilation and paired tail bounds.")),
                    Paragraph(Text("The gap tau is a finite zero-isolation certificate for the second catalog; it is not silently manufactured from floating-point samples. Likewise the finite catalog must represent the actual zero window completely. No numerical off-line zeta frame is asserted to exist."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitative-packet-mixed-majorant"),
                DeclarationHandle.Create(Prefix + "packet_majorant_of_uniform_jets"), H("The exact remaining scalar arithmetic input"),
                StatementSource.FromAuthor(Disp(F.Id("With common killer jets J0,J2 and a separately proved scalar tail bound Theta, C<=(3*r*(J0+J2))^2*(finite fourth-moment head+Theta)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This specializes the existing full mixed-majorant theorem and retains every cross term and one analytic multiplicity weight per zero. The quantitative packet constructor supplies the finite jets; the scalar infinite tail is still a number-theoretic input.")),
                    Paragraph(Text("The relevant external theorem is Brent, Platt and Trudgian, Accurate estimation of sums over zeros of the Riemann zeta-function, Mathematics of Computation 90 (2021), 2923-2935, Theorem 1, equations (1)-(3), DOI 10.1090/mcom/3652. Specializing its test weight to t^(-4) gives an explicit scalar tail. That theorem is not introduced as an axiom here, and its full zeta-specific proof has not been ported by this source. All new Lean sources remain Candidate without a compiler observation."))), DescribeRole.Theorem)), []));
}
