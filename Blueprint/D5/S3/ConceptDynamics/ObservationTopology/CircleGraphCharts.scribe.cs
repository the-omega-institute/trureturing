using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class CircleGraphChartsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An analytic intrinsic Circle map into a finite dimensional real inner product space "
            + "has actual immersion charts when its intrinsic differential is injective.",
        H("Intrinsic Circle Graph Charts"),
        Blocks(Describe.Lean(
            DescribeId.Create("circle-graph-chart-immersion"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts."
                    + "isImmersionOfComplement_of_contMDiff_injective_mvfderiv"),
            H("One fixed complement and actual normal form charts"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The ambient space V is a finite dimensional real inner product space. "
                        + "The map f is analytic: top in NatInfinityOmega is omega, "
                        + "whereas infinity denotes smooth regularity. R1 denotes the actual "
                        + "Circle model 𝓡 1, and I(Real,V) denotes the real self model 𝓘(ℝ, V). "
                        + "Its intrinsic differential is injective at every Circle point.")),
                Paragraph(Text(
                    "Fix E to be EuclideanSpace ℝ (Fin 1) and W to be "
                        + "EuclideanSpace ℝ (Fin (Module.finrank ℝ V - 1)), "
                        + "with subtraction in the natural numbers. In the formula, Real denotes "
                        + "ℝ and finrank denotes Module.finrank over the indicated field. "
                        + "At a Circle point z, let c = chartAt E z be the existing stereographic "
                        + "Circle chart, q = c(z), g = f ∘ c.symm, and D = fderiv ℝ g q. "
                        + "The orthogonal complement of D.range has the dimension of W. "
                        + "A continuous linear equivalence identifies it with W and extends D "
                        + "to a continuous linear equivalence L : (E × W) ≃L[ℝ] V "
                        + "satisfying L(u,0) = D(u) for every u in E.")),
                Paragraph(Text(
                    "Define H at L(u,w) to be g(u) plus L(0,w). "
                        + "The derivative of H at L(q,0) is the identity. The inverse "
                        + "function theorem supplies an actual open partial homeomorphism for H "
                        + "and proves the regularity of its inverse.")),
                Paragraph(Text(
                    "Restrict this inverse to an open set where both directions have the "
                        + "required regularity, and call the resulting ambient chart cod. "
                        + "Its forward and inverse regularity give membership in the ambient "
                        + "maximal atlas. Restrict c to the points whose L(u,0) lies in "
                        + "cod.target, and call the resulting domain chart dom.")),
                Paragraph(Text(
                    "These charts satisfy dom.source ⊆ f⁻¹(cod.source). For every u in "
                        + "dom.target, cod(f(dom.symm(u))) = L(u,0). The source inclusion "
                        + "follows from the ambient inverse mapping property. The exact chart "
                        + "equation follows from H(L(u,0)) = g(u) and cod.right_inv.")),
                Paragraph(Text(
                    "The construction uses the existing stereographic atlas, finite dimensional "
                        + "orthogonal decomposition, and inverse function theorem. This is the "
                        + "classical local graph construction for this intrinsic Circle model."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("intrinsic-paired-circle-sensor"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts.intrinsicSensor"),
                H("Actual intrinsic Circle sensor with real paired output"),
                StatementSource.FromAuthor(SensorDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite index type iota, k is a natural frequency family and a is a real "
                    + "amplitude family. Each Circle point z is the actual unit complex number, with "
                    + "the stereographic Circle manifold structure. The coordinate indexed by "
                    + "(i,0) is a(i) times the real part of z raised to k(i); coordinate (i,1) is a(i) "
                    + "times its imaginary part. The output V(iota) is EuclideanSpace Real (iota times Fin 2). "
                    + "The displayed coordZero and coordOne specify all real coordinates of that output; "
                    + "ofComplex denotes the ordinary Circle inclusion into the complex plane."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-paired-intrinsic-circle"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts.finite_paired_intrinsic_circle"),
                H("Analytic immersion and exact gcd criterion for embedding"),
                StatementSource.FromAuthor(SensorTheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The index type is finite and nonempty. Every k(i) is strictly positive and "
                        + "every a(i) is strictly positive. Distinct frequencies are allowed without "
                        + "further hypotheses; repeated frequencies are covered as well. The original "
                        + "finite nonempty subset of positive natural numbers is obtained by taking its "
                        + "subtype as the index and its inclusion as k. Finset.univ.gcd is the full gcd, "
                        + "not a pairwise coprimality requirement. W(iota) is EuclideanSpace Real "
                        + "(Fin (finrank Real V(iota) minus 1)), the same complement at every point.")),
                    Paragraph(Text(
                        "H in the formula abbreviates intrinsicSensor(k,a), and the displayed formula "
                        + "expands that abbreviation at each occurrence. The phase bridge is pointwise "
                        + "equality H(Circle.exp(phi)) = pairedSensor(k,a,phi). The auxiliary stateOfCircle "
                        + "map sends z to its two real coordinates, is injective, and at Circle.exp(phi) "
                        + "is exactly circleState(phi). Surjectivity of Circle.exp therefore transports "
                        + "the phase finite_paired_injective_iff_gcd_one criterion to intrinsic Circle injectivity.")),
                    Paragraph(Text(
                        "Equality of paired readings is equality of all harmonic powers; "
                        + "the finite gcd criterion follows by folding the power-gcd law. "
                        + "For gcd greater than one, the phase d=2 pi/gcd is distinct from zero "
                        + "on the physical circle and aliases at every common delay. Indeed, each "
                        + "frequency is divisible by the gcd, so shifting both phases by any real "
                        + "delay preserves equality of every harmonic power. The ordinary circle "
                        + "chord identity proves that the two physical states are distinct.")),
                    Paragraph(Text(
                        "The ambient polynomial is smooth and analytic. Recover coordinate pair i as "
                        + "the complex number Q(v) = v(i,0) + I v(i,1). Then Q composed with the ambient "
                        + "sensor is exactly a(i) z raised to k(i). Its real differential sends u to "
                        + "u times a(i) k(i) z raised to k(i)-1. This multiplier is nonzero because "
                        + "a(i)>0, k(i)>0, and a unit complex number is nonzero. The chain rule proves "
                        + "injectivity of the ambient sensor differential. The sphere inclusion "
                        + "has injective differential, so the intrinsic sensor does too. The actual "
                        + "CircleGraph theorem constructs immersion charts with the fixed W(iota).")),
                    Paragraph(Text(
                        "Compactness of Circle and the Hausdorff Euclidean codomain turn injectivity "
                        + "into a closed embedding. IsEmbedding.toHomeomorph gives the actual map to "
                        + "its range, with pointwise agreement explicitly in the theorem. Conversely, "
                        + "any agreeing homeomorphism forces injectivity, hence gcd one. Immersion "
                        + "holds for every positive nonempty family; it does not require gcd one. "
                        + "For a singleton frequency n>0, the map is immersed for every n and embedded "
                        + "exactly for n=1. Top is analytic regularity, which in particular supplies smoothness.")),
                    Paragraph(Text(
                        "For the original six-coordinate construction, set k=(2,3,4), "
                        + "Z=9+20 epsilon and a=(sqrt(epsilon),1,sqrt(epsilon))/sqrt(Z). "
                        + "For every epsilon>0 all amplitudes are positive and the gcd is one. "
                        + "The phase bridge identifies this intrinsic sensor after Circle.exp with "
                        + "the six real coordinates in frequency order 2, 3, 4 and these amplitudes. "
                        + "Its embedding pulls the Euclidean topology back to the existing intrinsic "
                        + "Circle topology. Thus every two positive epsilon values induce the same "
                        + "topology. Evaluation at phi minus pi/6 retains the original fixed delay. "
                        + "The finite-epsilon sharp lower-chord and correlation formulas have the "
                        + "separate quantitative range 0<epsilon<=1/2."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("V"), Comma, Sp, F.Id("f"), Colon, Sp,
        F.Id("Circle"), Sp, To, Sp, F.Id("V"), Comma, RowBreak, Grp(),
        Call("FiniteDimensionalRealInnerProductSpace", F.Id("V")), Sp,
        Land, Sp, Call("ContMDiff", F.Id("R1"), Call("I", F.Id("Real"), F.Id("V")), F.Id("top"), F.Id("f")),
        Sp, Land, Sp, Open, Forall, Sp, F.Id("z"), Comma, Sp,
        Call("Injective", Call("mvfderiv", F.Id("R1"), F.Id("f"), F.Id("z"))), Close,
        Sp, Rightarrow, RowBreak, Grp(),
        Call("IsImmersionOfComplement",
            Call("EuclideanSpace", F.Id("Real"),
                Call("Fin", Subtract(Call("finrank", F.Id("Real"), F.Id("V")), Num(1)))),
            F.Id("R1"), Call("I", F.Id("Real"), F.Id("V")), F.Id("top"), F.Id("f")),
        End, Grp(F.Id("gathered"))));

    private static Formula Real => F.Id("Real");
    private static Formula Index => F.Id("iota");
    private static Formula Frequency => F.Id("k");
    private static Formula Amplitude => F.Id("a");
    private static Formula Sensor => Call("intrinsicSensor", Frequency, Amplitude);
    private static Formula Output => Call("EuclideanSpace", Real,
        Seq(Index, Sp, Times, Sp, Call("Fin", Num(2))));
    private static Formula Complement => Call("EuclideanSpace", Real,
        Call("Fin", Subtract(Call("finrank", Real, Output), Num(1))));
    private static Formula FamilyBinders(bool nonempty) => Seq(
        Forall, Sp, Index, Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("Fintype", Index), CloseBracket,
        nonempty ? Seq(OpenBracket, Call("Nonempty", Index), CloseBracket) : Seq(),
        Sp, Frequency, Colon, Sp, Index, Sp, To, Sp, F.Id("Nat"), Comma, Sp,
        Amplitude, Colon, Sp, Index, Sp, To, Sp, Real, Comma, Sp);

    private static Formula SensorDefinitionFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), FamilyBinders(false), Forall, Sp, F.Id("z"), Colon, Sp, F.Id("Circle"), Comma, Sp,
        Forall, Sp, F.Id("i"), Colon, Sp, Index, Comma, RowBreak, Grp(),
        Call("coordZero", Call("intrinsicSensor", Frequency, Amplitude, F.Id("z")), F.Id("i")),
        Sp, Eq, Sp, Call("a", F.Id("i")), Sp, Cdot, Sp,
        Call("realPart", Call("pow", Call("ofComplex", F.Id("z")), Call("k", F.Id("i")))),
        Sp, Land, Sp,
        Call("coordOne", Call("intrinsicSensor", Frequency, Amplitude, F.Id("z")), F.Id("i")),
        Sp, Eq, Sp, Call("a", F.Id("i")), Sp, Cdot, Sp,
        Call("imagPart", Call("pow", Call("ofComplex", F.Id("z")), Call("k", F.Id("i")))),
        End, Grp(F.Id("gathered"))));

    private static Formula SensorTheoremFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), FamilyBinders(true), RowBreak, Grp(),
        Open, Forall, Sp, F.Id("i"), Colon, Sp, Index, Comma, Sp,
        Num(0), Sp, Lt, Sp, Call("k", F.Id("i")), Close, Sp, Land, Sp,
        Open, Forall, Sp, F.Id("i"), Colon, Sp, Index, Comma, Sp,
        Num(0), Sp, Lt, Sp, Call("a", F.Id("i")), Close,
        Sp, Rightarrow, RowBreak, Grp(),
        Open, Forall, Sp, F.Id("phi"), Colon, Sp, Real, Comma, Sp,
        Call("intrinsicSensor", Frequency, Amplitude, Call("CircleExp", F.Id("phi"))),
        Sp, Eq, Sp, Call("pairedSensor", Frequency, Amplitude, F.Id("phi")), Close,
        Sp, Land, RowBreak, Grp(),
        Call("ContMDiff", F.Id("R1"), Call("I", Real, Output), F.Id("top"), Sensor),
        Sp, Land, RowBreak, Grp(),
        Open, Forall, Sp, F.Id("z"), Colon, Sp, F.Id("Circle"), Comma, Sp,
        Call("Injective", Call("mvfderiv", F.Id("R1"), Sensor, F.Id("z"))), Close,
        Sp, Land, RowBreak, Grp(),
        Call("IsImmersionOfComplement", Complement, F.Id("R1"), Call("I", Real, Output),
            F.Id("top"), Sensor), Sp, Land, RowBreak, Grp(),
        Open, Call("IsEmbedding", Sensor), Sp, Iff, Sp,
        Call("gcd", Call("univ", Index), Frequency), Sp, Eq, Sp, Num(1), Close,
        Sp, Land, RowBreak, Grp(),
        Open, Open, Exists, Sp, F.Id("e"), Colon, Sp,
        Call("Homeomorph", F.Id("Circle"), Call("range", Sensor)), Comma, Sp,
        Forall, Sp, F.Id("z"), Colon, Sp, F.Id("Circle"), Comma, Sp,
        Call("val", Call("e", F.Id("z"))), Sp, Eq, Sp,
        Call("intrinsicSensor", Frequency, Amplitude, F.Id("z")), Close,
        Sp, Iff, Sp, Call("gcd", Call("univ", Index), Frequency), Sp, Eq, Sp, Num(1), Close,
        End, Grp(F.Id("gathered"))));

}
