using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PowerSeries;

internal sealed class DottieInverseSeriesDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Endpoint() => new Formula.Bind(FormulaQuantifier.Exists,
        FormulaIdentifier.Create("theta"), F.Id("Real"), Seq(
            D(0), Sp, Lt, Sp, F.Id("theta"), Sp, Land, Sp,
            F.Id("theta"), Sp, Lt, Sp, D(1), Sp, Land, Sp,
            Call("cos", F.Id("theta")), Sp, Eq, Sp, F.Id("theta"), Sp, Land, Sp,
            Seq(Open, All("t", F.Id("Real"), Seq(
                Seq(Open, D(0), Sp, Lt, Sp, F.Id("t"), Sp, Land, Sp,
                    Call("cos", F.Id("t")), Sp, Eq, Sp, F.Id("t"), Close), Sp, Implies, Sp,
                F.Id("t"), Sp, Eq, Sp, F.Id("theta"))), Close), Sp, Land, Sp,
            Call("Summable", Seq(F.Id("n"), Colon, Sp, F.Id("Nat"), Sp, Mapsto, Sp,
                Call("abs", Call("c", F.Id("n"))), Sp, Call("piPower", F.Id("n")))),
            Sp, Land, Sp,
            Call("HasSum", Seq(F.Id("n"), Colon, Sp, F.Id("Nat"), Sp, Mapsto, Sp,
                Call("c", F.Id("n")), Sp, Call("piPower", F.Id("n"))), F.Id("theta"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed rational inverse converges absolutely at pi to the unique positive cosine fixed point.",
        H("The prescribed rational inverse series"),
        Blocks(
            Describe.Lean(DescribeId.Create("dottie-arcsine-coefficients"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.alpha"),
                H("Rational coefficients in every degree"),
                StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), Seq(
                    Call("alpha", Seq(D(2), F.Id("n"))), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    Call("alpha", Seq(D(2), F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp,
                    Call("div", Call("choose", Seq(D(2), F.Id("n")), F.Id("n")),
                        Seq(D(4), Caret, Grp(F.Id("n")), Open,
                            D(2), F.Id("n"), Sp, Plus, Sp, D(1), Close)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient sequence alpha takes values in the rationals. Its even coefficients vanish and its degree 2n+1 coefficient is choose(2n,n)/(4^n(2n+1)). The definition selects these cases using the parity and integer half of the input degree."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-arcsine-series"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.arcsine"),
                H("The formal rational arcsine series"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("S"), Sp, Eq, Sp,
                    Call("mk", F.Id("alpha"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("S denotes PowerSeries.mk alpha over the rationals. Its coefficient in degree zero is zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-forward-series"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.forward"),
                H("The forward series"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("A"), Sp, Eq, Sp,
                    D(2), F.Id("X"), Sp, Plus, Sp, D(2), F.Id("S")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A is the literal rational formal series 2X+2S. Its constant coefficient is zero and its linear coefficient is 4, a unit in the rational field."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-prescribed-inverse"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.inverse"),
                H("The prescribed formal inverse"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("B"), Sp, Eq, Sp,
                    Call("substInvOfIsUnit", F.Id("A"), Call("unit", D(4)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B is exactly A.substInvOfIsUnit for the proof that the linear coefficient 4 is a unit. The choice of that proof does not alter the formal series."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-rational-inverse-endpoint"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.rational_inverse_endpoint"),
                H("Absolute convergence at pi and the positive fixed point"),
                StatementSource.FromAuthor(Disp(Endpoint())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/AnalyticClosure/kaplan2007dottie")),
                Blocks(
                    Paragraph(Text("Here c(n) is the real image of coefficient n of the literal rational series B, and piPower(n) means pi raised to n. Every natural degree, including zero, is included; no coefficient sign is discarded in HasSum. The unique positive cosine fixed point theta lies strictly between zero and one. Competitors t are arbitrary positive real numbers; no upper bound on t is assumed.")),
                    Paragraph(Text("Kaplan describes the rational pi series and the inverse-Taylor construction. The present proof supplies the complete all-coefficient connection, a single analytic branch with radius exceeding pi, absolute convergence and the all-positive uniqueness conclusion. No novelty or priority claim is made."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Connecting the selected analytic inverse"), Blocks(
                Paragraph(Text("For a complex function H analytic at zero and real on the real axis near zero, let h(y)=Re(H(y)) for real y. The real_taylor_data lemma supplies real analyticity of h and the real and imaginary parts of every complex derivative coefficient, including degree zero. Its Taylor series T has coefficient iteratedDeriv(n,h,0)/n!.")),
                Paragraph(Text("Suppose H(0)=0, the real function a(x)=2x+2arcsin(x) has the expansion given by A mapped to the reals, and a(h(y))=y near zero. Then T has zero constant coefficient. The scalar composition correspondence identifies the expansion of a composed with h with the realization of A substituted by T. Uniqueness of one-dimensional analytic expansions makes that substitution equal X. The mapped rational series B is another right formal inverse, by map_subst. Formal inverse uniqueness therefore gives T equal to B mapped to the reals. The same real_taylor_data coefficients then identify every complex derivative coefficient of H with the complex image of the corresponding rational coefficient of B.")),
                Paragraph(Text("A selected function is obtained from f(z)=z+sin(z). For norm(z)<=1, the pinned sine and cosine remainder bounds give norm(sin(z)-z)<=1/5 and norm(cos(z)-1)<=3/5. For norm(w)<7/4, the map z maps to (w+z-sin(z))/2 preserves the closed unit disk and has Lipschitz constant 3/10. Banach fixed-point existence, together with the same contraction estimate for uniqueness, defines a single inverse G(w) in the open unit disk. The nonzero derivative and the existing analytic local inverse identify that selection with an analytic inverse near each w. Conjugation and uniqueness make G real on real arguments, and G(0)=0. Thus H(Y)=sin(G(Y/2)) is analytic for norm(Y)<7/2, preserves real arguments and vanishes at zero. Cauchy supplies an expansion on radius 13/4. Termwise integration of the original normalized binomial series supplies the prescribed arcsine expansion for abs(x)<1. The principal arcsine identity on the real unit interval then gives 2*Re(H(y))+2*arcsin(Re(H(y)))=y for abs(y)<7/2. The original real_taylor_data and the live scalar composition correspondence identify every coefficient of this same H with B; expansion uniqueness then identifies the full Cauchy expansion with the scalar realization of B. Since pi<13/4, the existing convergence-radius theorem proves summability of abs(c(n))*pi^n. Evaluation of that expansion at pi and taking real parts proves HasSum with the signed coefficients.")),
                Paragraph(Text("For x=Re(G(pi/2)), the branch equation gives x+sin(x)=pi/2 and abs(x)<1. Nonpositivity of x would force sin(x)<=0, contradicting pi>0. Thus x>0 and theta=sin(x) satisfies 0<theta<x<1. The branch equation also gives theta=pi/2-x, hence cos(theta)=theta. Any positive fixed point t satisfies t<=1 from cos(t)<=1; strict decrease of cosine from zero excludes t=1. Cosine is antitone on [0,pi], so two positive fixed points in (0,1) cannot differ. This proves the uniqueness clause without restricting competitors in the theorem statement.")))))));
}
