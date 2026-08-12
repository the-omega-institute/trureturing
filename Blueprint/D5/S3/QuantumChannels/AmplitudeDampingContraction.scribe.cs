using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class AmplitudeDampingContractionDocument : IScribeDocumentDefinition
{
    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/QuantumChannels/AmplitudeDampingContraction",
            "For amplitude damping on the Bloch axis, the SLD coherence contraction ratio is the constant one minus gamma, while the RLD ratio is bounded by one in the open Bloch interval and tends to one at the pure-state boundary."),
        H("Amplitude-Damping Coherence Contraction Endpoints"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("amplitude-damping-is-affine-on-the-bloch-axis"),
                H("Amplitude damping is affine on the Bloch axis"),
                LeanDefinition(
                    "D5/S3/QuantumChannels/AmplitudeDampingContraction.dampedAxis"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The amplitude-damping parameter gamma sends an axial Bloch coordinate u "
                    + "to the affine coordinate u prime."))),
                Disp(Seq(
                    F.Id("u"), Apos, Eq, Open, D(1), Minus, Gamma, Close, F.Id("u"), Plus, Gamma))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("the-sld-radial-profile-is-constant"),
                H("The SLD radial profile is constant"),
                LeanDefinition(
                    "D5/S3/QuantumChannels/AmplitudeDampingContraction.sldRadialProfile"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The SLD radial profile assigns one to every axial coordinate."))),
                Disp(Seq(
                    Phi, Underscore, Grp(F.Id("SLD")), Open, F.Id("u"), Close, Eq, D(1)))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("the-km-radial-profile-is-the-hyperbolic-ratio"),
                H("The KM radial profile is the hyperbolic ratio"),
                LeanDefinition(
                    "D5/S3/QuantumChannels/AmplitudeDampingContraction.kmRadialProfile"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The KM radial profile is artanh of u divided by u away from zero, with "
                    + "its continuous value one assigned at zero."))),
                Disp(Seq(
                    Phi, Underscore, Grp(F.Id("KM")), Open, F.Id("u"), Close, Eq,
                    Operatorname, Grp(F.Id("artanh")), Open, F.Id("u"), Close,
                    Slash, F.Id("u"), Comma, Sp, F.Id("u"), Neq, D(0)))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("the-rld-radial-profile-has-a-quadratic-boundary-pole"),
                H("The RLD radial profile has a quadratic boundary pole"),
                LeanDefinition(
                    "D5/S3/QuantumChannels/AmplitudeDampingContraction.rldRadialProfile"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The RLD radial profile is the reciprocal of one minus the squared axial "
                    + "coordinate."))),
                Disp(Seq(
                    Phi, Underscore, Grp(F.Id("RLD")), Open, F.Id("u"), Close, Eq,
                    Frac, Grp(D(1)), Grp(D(1), Minus, F.Id("u"), Caret, D(2))))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create(
                    "the-coherence-ratio-compares-radial-profiles-before-and-after-damping"),
                H("The coherence ratio compares radial profiles before and after damping"),
                LeanDefinition(
                    "D5/S3/QuantumChannels/AmplitudeDampingContraction.coherenceRatio"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The axial coherence contraction ratio multiplies the profile quotient at "
                    + "the damped and original coordinates by one minus gamma."))),
                Disp(Seq(
                    F.Id("eta"), Underscore, Grp(Phi), Open, Gamma, Comma, F.Id("u"), Close, Eq,
                    Open, D(1), Minus, Gamma, Close,
                    Frac,
                    Grp(Phi, Open, F.Id("u"), Apos, Close),
                    Grp(Phi, Open, F.Id("u"), Close)))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create(
                    "a-pure-state-boundary-endpoint-combines-an-interior-bound-and-a-one-sided-limit"),
                H("A pure-state boundary endpoint combines an interior bound and a one-sided limit"),
                LeanDefinition(
                    "D5/S3/QuantumChannels/AmplitudeDampingContraction.HasPureBoundaryEndpoint"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A ratio has boundary endpoint b when it never exceeds b in the open Bloch "
                    + "interval and converges to b from below at the pure-state boundary."))),
                Disp(Seq(
                    Operatorname, Grp(F.Id("Endpoint")), Open, F.Id("r"), Comma, F.Id("b"), Close,
                    Leftrightarrow, Open,
                    Forall, Sp, F.Id("u"), InMacro, Open, Minus, D(1), Comma, D(1), Close,
                    Comma, Sp, F.Id("r"), Open, F.Id("u"), Close, Sp, Le, Sp, F.Id("b"), Close,
                    Sp, Land, Sp,
                    Lim, Underscore, Grp(F.Id("u"), To, D(1), Caret, Minus),
                    F.Id("r"), Open, F.Id("u"), Close, Eq, F.Id("b")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create(
                    "sld-is-constant-and-rld-reaches-the-unit-boundary-endpoint"),
                H("SLD is constant and RLD reaches the unit boundary endpoint"),
                LeanTheorem(
                    "D5/S3/QuantumChannels/AmplitudeDampingContraction."
                    + "amplitude_damping_sld_rld_endpoints"),
                Disp(Seq(
                    D(0), Le, Gamma, Lt, D(1), Rightarrow,
                    Open, Forall, Sp, F.Id("u"), Comma,
                    F.Id("eta"), Underscore, Grp(F.Id("SLD")), Open, Gamma, Comma, F.Id("u"), Close,
                    Eq, D(1), Minus, Gamma, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("u"), InMacro,
                    Open, Minus, D(1), Comma, D(1), Close, Comma,
                    F.Id("eta"), Underscore, Grp(F.Id("RLD")), Open, Gamma, Comma, F.Id("u"), Close,
                    Le, D(1), Close,
                    Sp, Land, Sp,
                    Lim, Underscore, Grp(F.Id("u"), To, D(1), Caret, Minus),
                    F.Id("eta"), Underscore, Grp(F.Id("RLD")), Open, Gamma, Comma, F.Id("u"), Close,
                    Eq, D(1))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For damping parameters from zero inclusive to one exclusive, the constant "
                    + "SLD profile makes its coherence ratio exactly one minus gamma at every "
                    + "axial coordinate. The RLD quotient simplifies inside the open interval "
                    + "to (1+u)/(1+u prime); the damped coordinate is at least u, so this ratio "
                    + "is at most one, and continuity gives the one-sided limit one as u "
                    + "approaches the pure-state boundary.")))
            ))));
}
