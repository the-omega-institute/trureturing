using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedRieszRepresentationDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => F.Id(n);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("K", Call("Type", V("u"))), Call("CompactHausdorffBorel", V("K")), Sp, Rightarrow),
        Seq(Grp(Seq(All("s", Call("SignedMeasure", V("K"))), All("t", Call("SignedMeasure", V("K"))),
            Call("Regular", Call("totalVariation", V("s"))), Sp, Land, Sp,
            Call("Regular", Call("totalVariation", V("t"))), Sp, Land, Sp,
            Call("signedFunctional", V("s")), Sp, Eq, Sp, Call("signedFunctional", V("t")),
            Sp, Rightarrow, Sp, V("s"), Sp, Eq, Sp, V("t"))), Sp, Land),
        Seq(Grp(Seq(All("s", Call("SignedMeasure", V("K"))),
            Call("Regular", Call("totalVariation", V("s"))), Sp, Rightarrow, Sp,
            Call("totalVariationRealUniv", V("s")), Sp, Eq, Sp,
            Call("norm", Call("signedFunctional", V("s"))))), Sp, Land),
        Grp(Seq(All("F", Call("StrongDual", Call("Real"), Call("ContinuousMap", V("K"), Call("Real")))),
            Exists, Sp, V("s"), Colon, Sp, Call("SignedMeasure", V("K")), Comma, Sp,
            Call("Regular", Call("totalVariation", V("s"))), Sp, Land, Sp,
            Call("signedFunctional", V("s")), Sp, Eq, Sp, V("F"), Sp, Land, Sp,
            Call("totalVariationRealUniv", V("s")), Sp, Eq, Sp, Call("norm", V("F"))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular signed measures form the real continuous dual of a compact Hausdorff Borel space, with exact total variation norm and uniqueness.",
        H("Real signed Riesz representation"),
        Blocks(
            Paragraph(Text(
                "K carries TopologicalSpace, CompactSpace, T2Space, MeasurableSpace and BorelSpace structures in an arbitrary universe. "
                + "The input F is an arbitrary StrongDual Real C(K,Real), with neither positivity nor nonzero norm assumed. "
                + "signedFunctional is the actual vector-measure signed integral used in NormPreservingLifts. "
                + "Regularity means regularity of the actual totalVariation measure. SignedMeasure already supplies its finiteness.")),
            Describe.Lean(
                DescribeId.Create("signed-riesz-markov-kakutani"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/SignedRieszRepresentation.signed_riesz_markov_kakutani"),
                H("Regular signed representation, uniqueness and exact norm"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/rudin1987riesz")),
                Blocks(
                    Paragraph(Text(
                        "For nonempty K define J(f,t) on the disjoint union of two copies of K by t+f on the left and t-f on the right. "
                        + "Its supremum norm is exactly abs(t)+norm(f). The upper inequality is the triangle inequality. "
                        + "For every x, one of the two values, with its sign chosen from the signs of t and f(x), has absolute value abs(t)+abs(f(x)). "
                        + "Taking the supremum gives the reverse inequality. J is injective, but is not an isometry for the usual maximum norm on C(K,Real) times Real.")),
                    Paragraph(Text(
                        "On the range of J define L(J(f,t))=F(f)+norm(F)*t. The norm identity bounds L by norm(F). "
                        + "Hahn–Banach gives a norm-preserving extension G to C(K disjoint-union K,Real). "
                        + "The unit is J(0,1), so G(1)=norm(F) and norm(G) is at most G(1). The order-unit positivity theorem makes G positive. "
                        + "Its restrictions to the two summands give positive functionals P,Q with P-Q=F and P(1)+Q(1)=norm(F).")),
                    Paragraph(Text(
                        "Positive Riesz–Markov–Kakutani on K gives finite regular measures mu and nu representing P and Q. "
                        + "Their real masses sum to norm(F). For s=mu.toSignedMeasure-nu.toSignedMeasure, the signed difference integral formula proves signedFunctional(s)=F. "
                        + "The scalar pairing is identified explicitly with its flipped pairing by commutativity of real multiplication.")),
                    Paragraph(Text(
                        "The variation inequality gives totalVariation(s) at most mu+nu. Finite domination transports compact inner approximation: "
                        + "for r less than rho(A), choose a compact closed C inside A with sigma(A minus C) less than rho(A)-r. "
                        + "Domination and the measurable partition of A force rho(C)>r. The finite Borel R1 regularity theorem then supplies regularity of rho. "
                        + "This applies to the signed variation dominated by the finite regular sum. Its mass is at most norm(F); the signed integration operator bound gives the reverse inequality.")),
                    Paragraph(Text(
                        "If K is empty, C(K,Real) and its dual are zero and the representative is zero. "
                        + "The nonempty construction divides by no quantity, so norm(F)=0 is included. No metric, separability or countable family of tests is required.")),
                    Paragraph(Text(
                        "For uniqueness let a,b be the positive and negative Jordan parts of s and d,e those of t. "
                        + "RegularSignedLift.regular_jordanParts_of_regular_totalVariation makes all four parts regular. "
                        + "Equal signed functionals give equal continuous integrals for the positive finite regular measures a+e and b+d. "
                        + "Measure.ext_of_integral_eq_on_compactlySupported identifies these sums. Applying Measure.toSignedMeasure_congr and "
                        + "Measure.toSignedMeasure_add, then the signed Jordan reconstruction, yields s=t. No regularity of s-t is assumed.")),
                    Paragraph(Text(
                        "For any regular signed s, apply the arbitrary-dual construction to signedFunctional(s). "
                        + "Its regular representative t has variation mass equal to the operator norm. Independently proved uniqueness gives t=s, "
                        + "so every regular signed measure has exact total variation norm. This argument uses only the one-sided integration bound in the construction, "
                        + "and does not use the universal norm identity to prove either existence or uniqueness."))),
                DescribeRole.Theorem))));
}
